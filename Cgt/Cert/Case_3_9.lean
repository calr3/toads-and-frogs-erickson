import Cgt.Certificate

/-! Machine-generated certificate: `T^3 □^9 F^3` is infinitesimal. -/

namespace Cgt.Cert_3_9
open Cell Game

theorem z_0 : le (tf [F, F, E, E, E, E, E, E, E, E, E, T, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, E, T, F, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1 : le (tf [F, E, F, E, E, E, E, E, E, E, T, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, T, E, F, T, T] [([F, E, F, E, E, E, E, E, E, E, E, T, F, T, T], [F, F, E, E, E, E, E, E, E, E, E, T, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_0 trivial)

theorem z_2 : le (tf [F, E, E, F, E, E, E, E, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, E, T, T, F, E, T] [([F, E, E, F, E, E, E, E, E, E, T, E, F, T, T], [F, E, F, E, E, E, E, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_3 : le (tf [F, E, E, E, F, E, E, E, E, E, T, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, E, T, T, F, T, E] [([F, E, E, E, F, E, E, E, E, E, T, T, F, E, T], [F, E, E, F, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_4 : le (tf [F, E, E, F, E, E, E, E, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, E, E, F, T, T] [([F, E, E, F, E, E, E, E, E, E, T, E, F, T, T], [F, E, F, E, E, E, E, E, E, E, T, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_5 : le (tf [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T] [([F, E, E, E, F, E, E, E, E, E, T, T, F, E, T], [F, E, E, F, E, E, E, E, E, E, T, T, F, E, T]), ([F, E, E, E, F, E, E, E, E, T, E, E, F, T, T], [F, E, E, F, E, E, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 (And.intro z_4 trivial))

theorem z_6 : le (tf [F, E, E, E, E, F, E, E, E, T, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, E, T, F, T, E] [([F, E, E, E, E, F, E, E, E, E, T, T, F, T, E], [F, E, E, E, F, E, E, E, E, E, T, T, F, T, E]), ([F, E, E, E, E, F, E, E, E, T, E, T, F, E, T], [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 (And.intro z_5 trivial))

theorem z_7 : le (tf [F, E, E, E, E, F, E, E, E, T, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, T, E, F, E, T] [([F, E, E, E, E, F, E, E, E, T, E, T, F, E, T], [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 trivial)

theorem z_8 : le (tf [F, E, E, E, E, E, F, E, E, T, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, T, T, E, F, T, E] [([F, E, E, E, E, E, F, E, E, T, E, T, F, T, E], [F, E, E, E, E, F, E, E, E, T, E, T, F, T, E]), ([F, E, E, E, E, E, F, E, E, T, T, E, F, E, T], [F, E, E, E, E, F, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 (And.intro z_7 trivial))

theorem z_9 : le (tf [F, E, E, E, E, E, E, F, E, T, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, T, T, T, F, E, E] [([F, E, E, E, E, E, E, F, E, T, T, E, F, T, E], [F, E, E, E, E, E, F, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 trivial)

theorem z_10 : le (tf [F, F, E, E, E, E, E, E, E, E, F, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, F, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_11 : le (tf [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T] [([F, F, E, E, E, E, E, E, E, E, E, F, T, T, T], [F, F, E, E, E, E, E, E, E, E, F, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_12 : le (tf [F, F, E, E, E, E, E, E, E, E, T, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, T, T, F, E, T] [([F, F, E, E, E, E, E, E, E, E, T, E, F, T, T], [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_13 : le (tf [F, E, F, E, E, E, E, E, E, E, T, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, T, T, F, T, E] [([F, E, F, E, E, E, E, E, E, E, T, T, F, E, T], [F, F, E, E, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 trivial)

theorem z_14 : le (tf [F, F, E, E, E, E, E, E, E, T, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, E, E, F, T, T] [([F, F, E, E, E, E, E, E, E, E, T, E, F, T, T], [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_15 : le (tf [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T] [([F, E, F, E, E, E, E, E, E, E, T, T, F, E, T], [F, F, E, E, E, E, E, E, E, E, T, T, F, E, T]), ([F, E, F, E, E, E, E, E, E, T, E, E, F, T, T], [F, F, E, E, E, E, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 (And.intro z_14 trivial))

theorem z_16 : le (tf [F, E, E, F, E, E, E, E, E, T, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, E, T, F, T, E] [([F, E, E, F, E, E, E, E, E, E, T, T, F, T, E], [F, E, F, E, E, E, E, E, E, E, T, T, F, T, E]), ([F, E, E, F, E, E, E, E, E, T, E, T, F, E, T], [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_15 trivial))

theorem z_17 : le (tf [F, E, E, F, E, E, E, E, E, T, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, T, E, F, E, T] [([F, E, E, F, E, E, E, E, E, T, E, T, F, E, T], [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_15 trivial)

theorem z_18 : le (tf [F, E, E, E, F, E, E, E, E, T, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, T, E, F, T, E] [([F, E, E, E, F, E, E, E, E, T, E, T, F, T, E], [F, E, E, F, E, E, E, E, E, T, E, T, F, T, E]), ([F, E, E, E, F, E, E, E, E, T, T, E, F, E, T], [F, E, E, F, E, E, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 (And.intro z_17 trivial))

theorem z_19 : le (tf [F, E, F, E, E, E, E, E, T, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, E, E, F, T, T] [([F, E, F, E, E, E, E, E, E, T, E, E, F, T, T], [F, F, E, E, E, E, E, E, E, T, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_14 trivial)

theorem z_20 : le (tf [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T] [([F, E, E, F, E, E, E, E, E, T, E, T, F, E, T], [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T]), ([F, E, E, F, E, E, E, E, T, E, E, E, F, T, T], [F, E, F, E, E, E, E, E, T, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_15 (And.intro z_19 trivial))

theorem z_21 : le (tf [F, E, E, E, F, E, E, E, T, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, E, T, F, T, E] [([F, E, E, E, F, E, E, E, E, T, E, T, F, T, E], [F, E, E, F, E, E, E, E, E, T, E, T, F, T, E]), ([F, E, E, E, F, E, E, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 (And.intro z_20 trivial))

theorem z_22 : le (tf [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T] [([F, E, E, E, F, E, E, E, E, T, T, E, F, E, T], [F, E, E, F, E, E, E, E, E, T, T, E, F, E, T]), ([F, E, E, E, F, E, E, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 (And.intro z_20 trivial))

theorem z_23 : le (tf [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E] [([F, E, E, E, E, F, E, E, E, T, T, E, F, T, E], [F, E, E, E, F, E, E, E, E, T, T, E, F, T, E]), ([F, E, E, E, E, F, E, E, T, E, E, T, F, T, E], [F, E, E, E, F, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, E, E, F, E, E, T, E, T, E, F, E, T], [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 (And.intro z_21 (And.intro z_22 trivial)))

theorem z_24 : le (tf [F, E, E, F, E, E, E, T, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, E, E, F, T, T] [([F, E, E, F, E, E, E, E, T, E, E, E, F, T, T], [F, E, F, E, E, E, E, E, T, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 trivial)

theorem z_25 : le (tf [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T] [([F, E, E, E, F, E, E, E, T, E, E, T, F, E, T], [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T]), ([F, E, E, E, F, E, E, T, E, E, E, E, F, T, T], [F, E, E, F, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 (And.intro z_24 trivial))

theorem z_26 : le (tf [F, E, E, E, E, F, E, T, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, E, T, F, T, E] [([F, E, E, E, E, F, E, E, T, E, E, T, F, T, E], [F, E, E, E, F, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, E, E, F, E, T, E, E, E, T, F, E, T], [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_21 (And.intro z_25 trivial))

theorem z_27 : le (tf [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T] [([F, E, E, E, E, F, E, E, T, E, T, E, F, E, T], [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T]), ([F, E, E, E, E, F, E, T, E, E, E, T, F, E, T], [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_25 trivial))

theorem z_28 : le (tf [F, E, E, E, E, E, F, T, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, E, T, E, F, T, E] [([F, E, E, E, E, E, F, E, T, E, T, E, F, T, E], [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E]), ([F, E, E, E, E, E, F, T, E, E, E, T, F, T, E], [F, E, E, E, E, F, E, T, E, E, E, T, F, T, E]), ([F, E, E, E, E, E, F, T, E, E, T, E, F, E, T], [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 (And.intro z_26 (And.intro z_27 trivial)))

theorem z_29 : le (tf [F, E, E, E, E, E, E, T, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, F, E, T, T, F, E, E] [([F, E, E, E, E, E, E, E, F, T, T, T, F, E, E], [F, E, E, E, E, E, E, F, E, T, T, T, F, E, E]), ([F, E, E, E, E, E, E, T, F, E, T, E, F, T, E], [F, E, E, E, E, E, F, T, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_9 (And.intro z_28 trivial))

theorem z_30 : le (tf [F, E, F, E, E, E, E, E, E, E, E, F, T, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, E, F, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_31 : le (tf [F, E, E, F, E, E, E, E, E, E, T, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, E, T, F, E, T, T] [([F, E, E, F, E, E, E, E, E, E, E, F, T, T, T], [F, E, F, E, E, E, E, E, E, E, E, F, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_30 trivial)

theorem z_32 : le (tf [F, E, E, E, F, E, E, E, E, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, E, T, F, T, E, T] [([F, E, E, E, F, E, E, E, E, E, T, F, E, T, T], [F, E, E, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 trivial)

theorem z_33 : le (tf [F, E, E, E, E, F, E, E, E, E, T, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, E, T, F, T, T, E] [([F, E, E, E, E, F, E, E, E, E, T, F, T, E, T], [F, E, E, E, F, E, E, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 trivial)

theorem z_34 : le (tf [F, E, E, E, F, E, E, E, E, T, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, E, F, E, T, T] [([F, E, E, E, F, E, E, E, E, E, T, F, E, T, T], [F, E, E, F, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 trivial)

theorem z_35 : le (tf [F, E, E, E, E, F, E, E, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, E, F, T, E, T] [([F, E, E, E, E, F, E, E, E, E, T, F, T, E, T], [F, E, E, E, F, E, E, E, E, E, T, F, T, E, T]), ([F, E, E, E, E, F, E, E, E, T, E, F, E, T, T], [F, E, E, E, F, E, E, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 (And.intro z_34 trivial))

theorem z_36 : le (tf [F, E, E, E, E, E, F, E, E, T, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, T, E, F, T, T, E] [([F, E, E, E, E, E, F, E, E, E, T, F, T, T, E], [F, E, E, E, E, F, E, E, E, E, T, F, T, T, E]), ([F, E, E, E, E, E, F, E, E, T, E, F, T, E, T], [F, E, E, E, E, F, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 (And.intro z_35 trivial))

theorem z_37 : le (tf [F, E, E, E, E, E, F, E, E, T, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, T, T, F, E, E, T] [([F, E, E, E, E, E, F, E, E, T, E, F, T, E, T], [F, E, E, E, E, F, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 trivial)

theorem z_38 : le (tf [F, E, E, E, E, E, E, F, E, T, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, T, T, F, E, T, E] [([F, E, E, E, E, E, E, F, E, T, E, F, T, T, E], [F, E, E, E, E, E, F, E, E, T, E, F, T, T, E]), ([F, E, E, E, E, E, E, F, E, T, T, F, E, E, T], [F, E, E, E, E, E, F, E, E, T, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_36 (And.intro z_37 trivial))

theorem z_39 : le (tf [F, E, F, E, E, E, E, E, E, E, T, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, T, F, T, E, T] [([F, E, F, E, E, E, E, E, E, E, T, F, E, T, T], [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_40 : le (tf [F, E, E, F, E, E, E, E, E, E, T, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, E, T, F, T, T, E] [([F, E, E, F, E, E, E, E, E, E, T, F, T, E, T], [F, E, F, E, E, E, E, E, E, E, T, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_39 trivial)

theorem z_41 : le (tf [F, E, F, E, E, E, E, E, E, T, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, E, F, E, T, T] [([F, E, F, E, E, E, E, E, E, E, T, F, E, T, T], [F, F, E, E, E, E, E, E, E, E, T, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 trivial)

theorem z_42 : le (tf [F, E, E, F, E, E, E, E, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, E, F, T, E, T] [([F, E, E, F, E, E, E, E, E, E, T, F, T, E, T], [F, E, F, E, E, E, E, E, E, E, T, F, T, E, T]), ([F, E, E, F, E, E, E, E, E, T, E, F, E, T, T], [F, E, F, E, E, E, E, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_39 (And.intro z_41 trivial))

theorem z_43 : le (tf [F, E, E, E, F, E, E, E, E, T, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, E, F, T, T, E] [([F, E, E, E, F, E, E, E, E, E, T, F, T, T, E], [F, E, E, F, E, E, E, E, E, E, T, F, T, T, E]), ([F, E, E, E, F, E, E, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_40 (And.intro z_42 trivial))

theorem z_44 : le (tf [F, E, E, F, E, E, E, E, T, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, E, F, E, T, T] [([F, E, E, F, E, E, E, E, E, T, E, F, E, T, T], [F, E, F, E, E, E, E, E, E, T, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_41 trivial)

theorem z_45 : le (tf [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T] [([F, E, E, E, F, E, E, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, E, E, T, E, F, T, E, T]), ([F, E, E, E, F, E, E, E, T, E, E, F, E, T, T], [F, E, E, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 (And.intro z_44 trivial))

theorem z_46 : le (tf [F, E, E, E, E, F, E, E, T, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, E, F, T, T, E] [([F, E, E, E, E, F, E, E, E, T, E, F, T, T, E], [F, E, E, E, F, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_43 (And.intro z_45 trivial))

theorem z_47 : le (tf [F, E, E, E, F, E, E, T, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, E, F, E, T, T] [([F, E, E, E, F, E, E, E, T, E, E, F, E, T, T], [F, E, E, F, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_44 trivial)

theorem z_48 : le (tf [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T] [([F, E, E, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T]), ([F, E, E, E, E, F, E, T, E, E, E, F, E, T, T], [F, E, E, E, F, E, E, T, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 (And.intro z_47 trivial))

theorem z_49 : le (tf [F, E, E, E, E, E, F, T, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, E, E, F, T, T, E] [([F, E, E, E, E, E, F, E, T, E, E, F, T, T, E], [F, E, E, E, E, F, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_48 trivial))

theorem z_50 : le (tf [F, E, E, E, F, E, E, E, E, T, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, T, F, E, E, T] [([F, E, E, E, F, E, E, E, E, T, E, F, T, E, T], [F, E, E, F, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 trivial)

theorem z_51 : le (tf [F, E, E, E, E, F, E, E, T, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, T, F, E, E, T] [([F, E, E, E, E, F, E, E, E, T, T, F, E, E, T], [F, E, E, E, F, E, E, E, E, T, T, F, E, E, T]), ([F, E, E, E, E, F, E, E, T, E, E, F, T, E, T], [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_50 (And.intro z_45 trivial))

theorem z_52 : le (tf [F, E, E, E, E, E, F, T, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, E, T, F, E, E, T] [([F, E, E, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, E, E, F, E, E, T, E, T, F, E, E, T]), ([F, E, E, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 (And.intro z_48 trivial))

theorem z_53 : le (tf [F, E, E, E, E, E, E, T, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, F, E, T, F, E, T, E] [([F, E, E, E, E, E, E, E, F, T, T, F, E, T, E], [F, E, E, E, E, E, E, F, E, T, T, F, E, T, E]), ([F, E, E, E, E, E, E, T, F, E, E, F, T, T, E], [F, E, E, E, E, E, F, T, E, E, E, F, T, T, E]), ([F, E, E, E, E, E, E, T, F, E, T, F, E, E, T], [F, E, E, E, E, E, F, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_38 (And.intro z_49 (And.intro z_52 trivial)))

theorem z_54 : le (tf [F, E, E, E, E, E, E, T, T, F, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, T, F, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_55 : le (tf [F, E, E, E, E, E, E, T, T, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, T, F, E, F, E, T, E] [([F, E, E, E, E, E, E, T, E, F, T, F, E, T, E], [F, E, E, E, E, E, E, T, F, E, T, F, E, T, E]), ([F, E, E, E, E, E, E, T, T, F, E, F, E, E, T], [F, E, E, E, E, E, E, T, T, F, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_53 (And.intro z_54 trivial))

theorem z_56 : le (tf [F, E, E, E, E, E, E, T, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, T, F, E, T, F, E, E] [([F, E, E, E, E, E, E, T, E, F, T, T, F, E, E], [F, E, E, E, E, E, E, T, F, E, T, T, F, E, E]), ([F, E, E, E, E, E, E, T, T, F, E, E, F, T, E], [F, E, E, E, E, E, E, T, T, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_55 trivial))

theorem z_57 : le (tf [F, E, E, E, E, E, E, T, T, T, F, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, T, T, F, E, F, E, E] [([F, E, E, E, E, E, E, T, T, E, F, T, F, E, E], [F, E, E, E, E, E, E, T, T, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_58 : le (tf [F, E, E, F, E, E, E, E, E, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, E, T, T, T, F, E] [([F, E, E, F, E, E, E, E, E, E, T, T, E, F, T], [F, E, E, F, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 trivial)

theorem z_59 : le (tf [F, E, E, E, F, E, E, E, E, T, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, E, T, T, F, E] [([F, E, E, E, F, E, E, E, E, E, T, T, T, F, E], [F, E, E, F, E, E, E, E, E, E, T, T, T, F, E]), ([F, E, E, E, F, E, E, E, E, T, E, T, E, F, T], [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_58 (And.intro z_5 trivial))

theorem z_60 : le (tf [F, E, E, E, E, F, E, E, E, T, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, T, E, T, F, E] [([F, E, E, E, E, F, E, E, E, T, E, T, T, F, E], [F, E, E, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, E, E, F, E, E, E, T, T, E, E, F, T], [F, E, E, E, E, F, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 (And.intro z_7 trivial))

theorem z_61 : le (tf [F, E, E, E, F, E, E, E, T, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, E, T, E, F, T] [([F, E, E, E, F, E, E, E, E, T, E, T, E, F, T], [F, E, E, E, F, E, E, E, E, T, E, T, F, E, T]), ([F, E, E, E, F, E, E, E, T, E, E, E, T, F, T], [F, E, E, E, F, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 (And.intro z_45 trivial))

theorem z_62 : le (tf [F, E, E, E, E, F, E, E, T, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, E, T, T, F, E] [([F, E, E, E, E, F, E, E, E, T, E, T, T, F, E], [F, E, E, E, F, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, E, E, F, E, E, E, T, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 (And.intro z_61 trivial))

theorem z_63 : le (tf [F, E, E, E, E, F, E, E, T, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, T, E, E, F, T] [([F, E, E, E, E, F, E, E, E, T, T, E, E, F, T], [F, E, E, E, E, F, E, E, E, T, T, E, F, E, T]), ([F, E, E, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, E, E, F, E, E, E, T, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 (And.intro z_61 trivial))

theorem z_64 : le (tf [F, E, E, E, E, E, F, E, T, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, E, T, E, T, F, E] [([F, E, E, E, E, E, F, E, E, T, T, E, T, F, E], [F, E, E, E, E, F, E, E, E, T, T, E, T, F, E]), ([F, E, E, E, E, E, F, E, T, E, E, T, T, F, E], [F, E, E, E, E, F, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, E, E, F, E, T, E, T, E, E, F, T], [F, E, E, E, E, F, E, E, T, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_60 (And.intro z_62 (And.intro z_63 trivial)))

theorem z_65 : le (tf [F, F, E, E, E, E, E, E, E, E, T, T, T, F, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, T, T, T, F, E] [([F, F, E, E, E, E, E, E, E, E, T, T, E, F, T], [F, F, E, E, E, E, E, E, E, E, T, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 trivial)

theorem z_66 : le (tf [F, E, F, E, E, E, E, E, E, T, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, E, T, T, F, E] [([F, E, F, E, E, E, E, E, E, E, T, T, T, F, E], [F, F, E, E, E, E, E, E, E, E, T, T, T, F, E]), ([F, E, F, E, E, E, E, E, E, T, E, T, E, F, T], [F, E, F, E, E, E, E, E, E, T, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 (And.intro z_15 trivial))

theorem z_67 : le (tf [F, E, E, F, E, E, E, E, T, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, E, T, T, F, E] [([F, E, E, F, E, E, E, E, E, T, E, T, T, F, E], [F, E, F, E, E, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, F, E, E, E, E, T, E, E, T, E, F, T], [F, E, E, F, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_20 trivial))

theorem z_68 : le (tf [F, E, E, E, F, E, E, T, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, E, T, T, F, E] [([F, E, E, E, F, E, E, E, T, E, E, T, T, F, E], [F, E, E, F, E, E, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, F, E, E, T, E, E, E, T, E, F, T], [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_25 trivial))

theorem z_69 : le (tf [F, F, E, E, E, E, F, E, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_70 : le (tf [F, F, E, E, E, E, E, F, E, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, E, E, T, E, T, T] [([F, F, E, E, E, E, E, F, E, E, E, E, T, T, T], [F, F, E, E, E, E, F, E, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 trivial)

theorem z_71 : le (tf [F, F, E, E, E, E, E, E, F, E, E, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, E, T, T, E, T] [([F, F, E, E, E, E, E, E, F, E, E, T, E, T, T], [F, F, E, E, E, E, E, F, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 trivial)

theorem z_72 : le (tf [F, F, E, E, E, E, E, E, F, E, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, T, E, E, T, T] [([F, F, E, E, E, E, E, E, F, E, E, T, E, T, T], [F, F, E, E, E, E, E, F, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 trivial)

theorem z_73 : le (tf [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T] [([F, F, E, E, E, E, E, E, E, F, E, T, T, E, T], [F, F, E, E, E, E, E, E, F, E, E, T, T, E, T]), ([F, F, E, E, E, E, E, E, E, F, T, E, E, T, T], [F, F, E, E, E, E, E, E, F, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 (And.intro z_72 trivial))

theorem z_74 : le (tf [F, F, E, E, E, E, E, E, F, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_75 : le (tf [F, F, E, E, E, E, E, E, E, F, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, F, E, T, E, T, T] [([F, F, E, E, E, E, E, E, E, F, E, E, T, T, T], [F, F, E, E, E, E, E, E, F, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 trivial)

theorem z_76 : le (tf [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T] [([F, F, E, E, E, E, E, E, E, E, F, T, E, T, T], [F, F, E, E, E, E, E, E, E, F, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 trivial)

theorem z_77 : le (tf [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T] [([F, F, E, E, E, E, E, E, E, E, T, F, T, E, T], [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T]), ([F, F, E, E, E, E, E, E, E, T, E, F, E, T, T], [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 (And.intro z_76 trivial))

theorem z_78 : le (tf [F, F, E, E, E, E, E, E, T, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, E, E, T, F, T] [([F, F, E, E, E, E, E, E, E, T, E, E, T, F, T], [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 trivial)

theorem z_79 : le (tf [F, E, F, E, E, E, E, T, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, E, E, T, F, T] [([F, E, F, E, E, E, E, E, T, E, E, E, T, F, T], [F, F, E, E, E, E, E, E, T, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_78 trivial)

theorem z_80 : le (tf [F, E, E, F, E, E, T, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, E, E, T, F, T] [([F, E, E, F, E, E, E, T, E, E, E, E, T, F, T], [F, E, F, E, E, E, E, T, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 trivial)

theorem z_81 : le (tf [F, E, E, E, F, E, T, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, E, T, E, F, T] [([F, E, E, E, F, E, E, T, E, E, E, T, E, F, T], [F, E, E, E, F, E, E, T, E, E, E, T, F, E, T]), ([F, E, E, E, F, E, T, E, E, E, E, E, T, F, T], [F, E, E, F, E, E, T, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_80 trivial))

theorem z_82 : le (tf [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E] [([F, E, E, E, E, F, E, T, E, E, E, T, T, F, E], [F, E, E, E, F, E, E, T, E, E, E, T, T, F, E]), ([F, E, E, E, E, F, T, E, E, E, E, T, E, F, T], [F, E, E, E, F, E, T, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 (And.intro z_81 trivial))

theorem z_83 : le (tf [F, E, E, E, E, F, T, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, E, E, F, T] [([F, E, E, E, E, F, E, T, E, E, T, E, E, F, T], [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T]), ([F, E, E, E, E, F, T, E, E, E, E, T, E, F, T], [F, E, E, E, F, E, T, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 (And.intro z_81 trivial))

theorem z_84 : le (tf [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E] [([F, E, E, E, E, E, E, F, T, E, T, E, T, F, E], [F, E, E, E, E, E, F, E, T, E, T, E, T, F, E]), ([F, E, E, E, E, E, T, F, E, E, E, T, T, F, E], [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]), ([F, E, E, E, E, E, T, F, E, E, T, E, E, F, T], [F, E, E, E, E, F, T, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_82 (And.intro z_83 trivial)))

theorem z_85 : le (tf [F, E, E, E, E, E, T, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, E, T, T, E, F, E] [([F, E, E, E, E, E, E, T, F, E, T, T, E, F, E], [F, E, E, E, E, E, E, T, F, E, T, T, F, E, E]), ([F, E, E, E, E, E, T, E, F, E, T, E, T, F, E], [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_84 trivial))

theorem z_86 : le (tf [F, F, E, E, F, E, E, E, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_87 : le (tf [F, F, E, E, E, F, E, E, E, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, E, E, T, E, T, T] [([F, F, E, E, E, F, E, E, E, E, E, E, T, T, T], [F, F, E, E, F, E, E, E, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_86 trivial)

theorem z_88 : le (tf [F, F, E, E, E, E, F, E, E, E, E, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, E, T, T, E, T] [([F, F, E, E, E, E, F, E, E, E, E, T, E, T, T], [F, F, E, E, E, F, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_87 trivial)

theorem z_89 : le (tf [F, F, E, E, E, E, E, F, E, E, E, T, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, E, E, T, T, T, E] [([F, F, E, E, E, E, E, F, E, E, E, T, T, E, T], [F, F, E, E, E, E, F, E, E, E, E, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 trivial)

theorem z_90 : le (tf [F, F, E, E, E, E, F, E, E, E, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, T, E, E, T, T] [([F, F, E, E, E, E, F, E, E, E, E, T, E, T, T], [F, F, E, E, E, F, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_87 trivial)

theorem z_91 : le (tf [F, F, E, E, E, E, E, F, E, E, T, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, E, T, E, T, E, T] [([F, F, E, E, E, E, E, F, E, E, E, T, T, E, T], [F, F, E, E, E, E, F, E, E, E, E, T, T, E, T]), ([F, F, E, E, E, E, E, F, E, E, T, E, E, T, T], [F, F, E, E, E, E, F, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 (And.intro z_90 trivial))

theorem z_92 : le (tf [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E] [([F, F, E, E, E, E, E, E, F, E, E, T, T, T, E], [F, F, E, E, E, E, E, F, E, E, E, T, T, T, E]), ([F, F, E, E, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, E, E, F, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_89 (And.intro z_91 trivial))

theorem z_93 : le (tf [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T] [([F, F, E, E, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, E, E, F, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 trivial)

theorem z_94 : le (tf [F, F, E, E, E, E, E, E, E, F, T, T, E, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, F, T, T, E, T, E] [([F, F, E, E, E, E, E, E, E, F, T, E, T, T, E], [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E]), ([F, F, E, E, E, E, E, E, E, F, T, T, E, E, T], [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_93 trivial))

theorem z_95 : le (tf [F, E, F, E, E, E, E, E, E, F, T, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, F, T, T, T, E, E] [([F, E, F, E, E, E, E, E, E, F, T, T, E, T, E], [F, F, E, E, E, E, E, E, E, F, T, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 trivial)

theorem z_96 : le (tf [F, F, F, E, E, E, E, E, E, E, E, E, T, T, T]) zero :=
  le_zero_of_pairs [F, F, F, E, E, E, E, E, E, E, E, E, T, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_97 : le (tf [F, F, E, F, E, E, E, E, E, E, E, T, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, F, E, E, E, E, E, E, E, T, E, T, T] [([F, F, E, F, E, E, E, E, E, E, E, E, T, T, T], [F, F, F, E, E, E, E, E, E, E, E, E, T, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 trivial)

theorem z_98 : le (tf [F, F, E, E, F, E, E, E, E, E, E, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, E, E, E, T, T, E, T] [([F, F, E, E, F, E, E, E, E, E, E, T, E, T, T], [F, F, E, F, E, E, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_97 trivial)

theorem z_99 : le (tf [F, F, E, E, F, E, E, E, E, E, T, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, F, E, E, E, E, E, T, E, E, T, T] [([F, F, E, E, F, E, E, E, E, E, E, T, E, T, T], [F, F, E, F, E, E, E, E, E, E, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_97 trivial)

theorem z_100 : le (tf [F, F, E, E, E, F, E, E, E, E, T, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, E, T, E, T, E, T] [([F, F, E, E, E, F, E, E, E, E, E, T, T, E, T], [F, F, E, E, F, E, E, E, E, E, E, T, T, E, T]), ([F, F, E, E, E, F, E, E, E, E, T, E, E, T, T], [F, F, E, E, F, E, E, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 (And.intro z_99 trivial))

theorem z_101 : le (tf [F, F, E, E, E, F, E, E, E, T, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, T, E, E, E, T, T] [([F, F, E, E, E, F, E, E, E, E, T, E, E, T, T], [F, F, E, E, F, E, E, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_99 trivial)

theorem z_102 : le (tf [F, F, E, E, E, E, F, E, E, T, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, T, E, E, T, E, T] [([F, F, E, E, E, E, F, E, E, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, E, E, T, E, T, E, T]), ([F, F, E, E, E, E, F, E, E, T, E, E, E, T, T], [F, F, E, E, E, F, E, E, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 (And.intro z_101 trivial))

theorem z_103 : le (tf [F, F, E, E, E, E, F, E, T, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, T, E, E, E, E, T, T] [([F, F, E, E, E, E, F, E, E, T, E, E, E, T, T], [F, F, E, E, E, F, E, E, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_101 trivial)

theorem z_104 : le (tf [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T] [([F, F, E, E, E, E, E, F, E, T, E, E, T, E, T], [F, F, E, E, E, E, F, E, E, T, E, E, T, E, T]), ([F, F, E, E, E, E, E, F, T, E, E, E, E, T, T], [F, F, E, E, E, E, F, E, T, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_102 (And.intro z_103 trivial))

theorem z_105 : le (tf [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E] [([F, F, E, E, E, E, E, E, E, F, T, E, T, T, E], [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E]), ([F, F, E, E, E, E, E, E, T, F, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_104 trivial))

theorem z_106 : le (tf [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T] [([F, F, E, E, E, E, E, E, E, F, T, T, E, E, T], [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T]), ([F, F, E, E, E, E, E, E, T, F, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_104 trivial))

theorem z_107 : le (tf [F, E, F, E, E, E, E, E, T, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, F, E, T, E, T, E] [([F, E, F, E, E, E, E, E, E, F, T, T, E, T, E], [F, F, E, E, E, E, E, E, E, F, T, T, E, T, E]), ([F, E, F, E, E, E, E, E, T, F, E, E, T, T, E], [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E]), ([F, E, F, E, E, E, E, E, T, F, E, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 (And.intro z_105 (And.intro z_106 trivial)))

theorem z_108 : le (tf [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E] [([F, E, E, F, E, E, E, E, E, F, T, T, T, E, E], [F, E, F, E, E, E, E, E, E, F, T, T, T, E, E]), ([F, E, E, F, E, E, E, E, T, F, E, T, E, T, E], [F, E, F, E, E, E, E, E, T, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 (And.intro z_107 trivial))

theorem z_109 : le (tf [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T] [([F, E, F, E, E, E, E, E, T, F, E, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 trivial)

theorem z_110 : le (tf [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E] [([F, E, E, F, E, E, E, E, T, F, E, T, E, T, E], [F, E, F, E, E, E, E, E, T, F, E, T, E, T, E]), ([F, E, E, F, E, E, E, E, T, F, T, E, E, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_109 trivial))

theorem z_111 : le (tf [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E] [([F, E, E, E, F, E, E, E, T, F, E, T, T, E, E], [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E]), ([F, E, E, E, F, E, E, E, T, F, T, E, E, T, E], [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_110 trivial))

theorem z_112 : le (tf [F, E, F, E, E, E, E, E, T, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, E, F, E, E, T] [([F, E, F, E, E, E, E, E, T, E, T, F, E, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 trivial)

theorem z_113 : le (tf [F, E, E, F, E, E, E, E, T, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, E, F, E, T, E] [([F, E, E, F, E, E, E, E, T, E, T, F, E, T, E], [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E]), ([F, E, E, F, E, E, E, E, T, T, E, F, E, E, T], [F, E, F, E, E, E, E, E, T, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 (And.intro z_112 trivial))

theorem z_114 : le (tf [F, E, E, E, F, E, E, E, T, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, E, F, T, E, E] [([F, E, E, E, F, E, E, E, T, E, T, F, T, E, E], [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E]), ([F, E, E, E, F, E, E, E, T, T, E, F, E, T, E], [F, E, E, F, E, E, E, E, T, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 (And.intro z_113 trivial))

theorem z_115 : le (tf [F, F, E, E, E, E, E, E, E, F, E, T, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, F, E, T, T, T, E] [([F, F, E, E, E, E, E, E, E, F, E, T, T, E, T], [F, F, E, E, E, E, E, E, F, E, E, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 trivial)

theorem z_116 : le (tf [F, F, E, E, E, E, E, F, E, T, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, T, E, E, E, T, T] [([F, F, E, E, E, E, E, F, E, E, T, E, E, T, T], [F, F, E, E, E, E, F, E, E, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 trivial)

theorem z_117 : le (tf [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T] [([F, F, E, E, E, E, E, E, F, E, T, E, T, E, T], [F, F, E, E, E, E, E, F, E, E, T, E, T, E, T]), ([F, F, E, E, E, E, E, E, F, T, E, E, E, T, T], [F, F, E, E, E, E, E, F, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 (And.intro z_116 trivial))

theorem z_118 : le (tf [F, F, E, E, E, E, E, E, E, T, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, F, E, T, T, E] [([F, F, E, E, E, E, E, E, E, E, F, T, T, T, E], [F, F, E, E, E, E, E, E, E, F, E, T, T, T, E]), ([F, F, E, E, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 (And.intro z_117 trivial))

theorem z_119 : le (tf [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T] [([F, F, E, E, E, E, E, E, E, F, T, E, E, T, T], [F, F, E, E, E, E, E, E, F, E, T, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_120 : le (tf [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T] [([F, F, E, E, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T]), ([F, F, E, E, E, E, E, E, T, E, F, E, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 (And.intro z_119 trivial))

theorem z_121 : le (tf [F, F, E, E, E, E, E, E, T, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, E, F, T, T, E] [([F, F, E, E, E, E, E, E, E, T, E, F, T, T, E], [F, F, E, E, E, E, E, E, E, T, F, E, T, T, E]), ([F, F, E, E, E, E, E, E, T, E, E, F, T, E, T], [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_120 trivial))

theorem z_122 : le (tf [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T] [([F, F, E, E, E, E, E, E, T, E, F, E, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_119 trivial)

theorem z_123 : le (tf [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T] [([F, F, E, E, E, E, E, E, T, E, E, F, T, E, T], [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T]), ([F, F, E, E, E, E, E, T, E, E, E, F, E, T, T], [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 (And.intro z_122 trivial))

theorem z_124 : le (tf [F, E, F, E, E, E, E, T, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, E, F, T, T, E] [([F, E, F, E, E, E, E, E, T, E, E, F, T, T, E], [F, F, E, E, E, E, E, E, T, E, E, F, T, T, E]), ([F, E, F, E, E, E, E, T, E, E, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_121 (And.intro z_123 trivial))

theorem z_125 : le (tf [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T] [([F, E, F, E, E, E, E, E, T, E, T, F, E, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T]), ([F, E, F, E, E, E, E, T, E, E, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 (And.intro z_123 trivial))

theorem z_126 : le (tf [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E] [([F, E, E, F, E, E, E, E, T, E, T, F, E, T, E], [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E]), ([F, E, E, F, E, E, E, T, E, E, E, F, T, T, E], [F, E, F, E, E, E, E, T, E, E, E, F, T, T, E]), ([F, E, E, F, E, E, E, T, E, E, T, F, E, E, T], [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 (And.intro z_124 (And.intro z_125 trivial)))

theorem z_127 : le (tf [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E] [([F, E, E, E, F, E, E, E, T, E, T, F, T, E, E], [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E]), ([F, E, E, E, F, E, E, T, E, E, T, F, E, T, E], [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 (And.intro z_126 trivial))

theorem z_128 : le (tf [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T] [([F, F, E, E, E, E, E, E, E, T, F, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 trivial)

theorem z_129 : le (tf [F, F, E, E, E, E, E, E, E, T, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, T, T, E, F, E, T] [([F, F, E, E, E, E, E, E, E, T, E, T, F, E, T], [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 trivial)

theorem z_130 : le (tf [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T] [([F, F, E, E, E, E, E, E, E, T, E, F, E, T, T], [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 trivial)

theorem z_131 : le (tf [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T] [([F, F, E, E, E, E, E, E, E, T, E, T, F, E, T], [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T]), ([F, F, E, E, E, E, E, E, T, E, E, E, F, T, T], [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 (And.intro z_130 trivial))

theorem z_132 : le (tf [F, F, E, E, E, E, E, E, T, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, T, E, E, F, T] [([F, F, E, E, E, E, E, E, E, T, T, E, E, F, T], [F, F, E, E, E, E, E, E, E, T, T, E, F, E, T]), ([F, F, E, E, E, E, E, E, T, E, E, T, E, F, T], [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_131 trivial))

theorem z_133 : le (tf [F, E, F, E, E, E, E, E, T, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, E, E, E, F, T] [([F, E, F, E, E, E, E, E, T, E, T, E, E, F, T], [F, F, E, E, E, E, E, E, T, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 trivial)

theorem z_134 : le (tf [F, F, E, E, E, E, E, T, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, E, T, E, F, T] [([F, F, E, E, E, E, E, E, T, E, E, T, E, F, T], [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T]), ([F, F, E, E, E, E, E, T, E, E, E, E, T, F, T], [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_123 trivial))

theorem z_135 : le (tf [F, E, F, E, E, E, E, T, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, T, E, E, F, T] [([F, E, F, E, E, E, E, E, T, E, T, E, E, F, T], [F, F, E, E, E, E, E, E, T, E, T, E, E, F, T]), ([F, E, F, E, E, E, E, T, E, E, E, T, E, F, T], [F, F, E, E, E, E, E, T, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 (And.intro z_134 trivial))

theorem z_136 : le (tf [F, E, E, F, E, E, E, T, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, E, E, E, F, T] [([F, E, E, F, E, E, E, E, T, T, E, E, E, F, T], [F, E, F, E, E, E, E, E, T, T, E, E, E, F, T]), ([F, E, E, F, E, E, E, T, E, E, T, E, E, F, T], [F, E, F, E, E, E, E, T, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 (And.intro z_135 trivial))

theorem z_137 : le (tf [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E] [([F, E, E, E, F, E, E, E, T, T, E, E, T, F, E], [F, E, E, E, F, E, E, E, T, T, E, F, T, E, E]), ([F, E, E, E, F, E, E, T, E, E, T, E, T, F, E], [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E]), ([F, E, E, E, F, E, E, T, E, T, E, E, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 (And.intro z_127 (And.intro z_136 trivial)))

theorem z_138 : le (tf [F, F, E, E, E, E, T, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, E, E, F, E, T, T] [([F, F, E, E, E, E, E, T, E, E, E, F, E, T, T], [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_122 trivial)

theorem z_139 : le (tf [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T] [([F, E, F, E, E, E, E, T, E, E, E, F, T, E, T], [F, F, E, E, E, E, E, T, E, E, E, F, T, E, T]), ([F, E, F, E, E, E, T, E, E, E, E, F, E, T, T], [F, F, E, E, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_123 (And.intro z_138 trivial))

theorem z_140 : le (tf [F, E, E, F, E, E, T, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, E, F, T, T, E] [([F, E, E, F, E, E, E, T, E, E, E, F, T, T, E], [F, E, F, E, E, E, E, T, E, E, E, F, T, T, E]), ([F, E, E, F, E, E, T, E, E, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_124 (And.intro z_139 trivial))

theorem z_141 : le (tf [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T] [([F, E, E, F, E, E, E, T, E, E, T, F, E, E, T], [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T]), ([F, E, E, F, E, E, T, E, E, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_125 (And.intro z_139 trivial))

theorem z_142 : le (tf [F, E, E, E, F, E, T, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, T, F, E, T, E] [([F, E, E, E, F, E, E, T, E, E, T, F, E, T, E], [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E]), ([F, E, E, E, F, E, T, E, E, E, E, F, T, T, E], [F, E, E, F, E, E, T, E, E, E, E, F, T, T, E]), ([F, E, E, E, F, E, T, E, E, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 (And.intro z_140 (And.intro z_141 trivial)))

theorem z_143 : le (tf [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E] [([F, E, E, E, E, F, E, T, E, E, T, F, T, E, E], [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E]), ([F, E, E, E, E, F, T, E, E, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_127 (And.intro z_142 trivial))

theorem z_144 : le (tf [F, E, F, E, E, E, T, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, E, T, E, F, T] [([F, E, F, E, E, E, E, T, E, E, E, T, E, F, T], [F, F, E, E, E, E, E, T, E, E, E, T, E, F, T]), ([F, E, F, E, E, E, T, E, E, E, E, E, T, F, T], [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_134 (And.intro z_139 trivial))

theorem z_145 : le (tf [F, E, E, F, E, E, T, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, T, E, E, F, T] [([F, E, E, F, E, E, E, T, E, E, T, E, E, F, T], [F, E, F, E, E, E, E, T, E, E, T, E, E, F, T]), ([F, E, E, F, E, E, T, E, E, E, E, T, E, F, T], [F, E, F, E, E, E, T, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_135 (And.intro z_144 trivial))

theorem z_146 : le (tf [F, E, E, E, F, E, T, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, T, E, E, E, F, T] [([F, E, E, E, F, E, E, T, E, T, E, E, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, E, E, F, T]), ([F, E, E, E, F, E, T, E, E, E, T, E, E, F, T], [F, E, E, F, E, E, T, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 (And.intro z_145 trivial))

theorem z_147 : le (tf [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E] [([F, E, E, E, E, F, E, T, E, T, E, E, T, F, E], [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E]), ([F, E, E, E, E, F, T, E, E, E, T, E, T, F, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]), ([F, E, E, E, E, F, T, E, E, T, E, E, E, F, T], [F, E, E, E, F, E, T, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 (And.intro z_143 (And.intro z_146 trivial)))

theorem z_148 : le (tf [F, E, E, E, F, E, E, T, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, E, E, F, T] [([F, E, E, E, F, E, E, T, E, T, E, E, E, F, T], [F, E, E, F, E, E, E, T, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 trivial)

theorem z_149 : le (tf [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T] [([F, E, E, E, E, F, E, T, T, E, E, E, E, F, T], [F, E, E, E, F, E, E, T, T, E, E, E, E, F, T]), ([F, E, E, E, E, F, T, E, E, T, E, E, E, F, T], [F, E, E, E, F, E, T, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 (And.intro z_146 trivial))

theorem z_150 : le (tf [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E] [([F, E, E, E, E, E, T, F, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]), ([F, E, E, E, E, E, T, F, T, E, E, E, E, F, T], [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 (And.intro z_149 trivial))

theorem z_151 : le (tf [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E] [([F, E, E, E, E, E, E, T, T, F, E, T, E, F, E], [F, E, E, E, E, E, E, T, T, F, E, T, F, E, E]), ([F, E, E, E, E, E, T, E, E, F, T, T, E, F, E], [F, E, E, E, E, E, T, E, F, E, T, T, E, F, E]), ([F, E, E, E, E, E, T, E, T, F, E, E, T, F, E], [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 (And.intro z_85 (And.intro z_150 trivial)))

theorem z_152 : le (tf [F, E, E, E, E, E, T, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, T, T, F, E, E, F, E] [([F, E, E, E, E, E, E, T, T, T, F, E, E, F, E], [F, E, E, E, E, E, E, T, T, T, F, E, F, E, E]), ([F, E, E, E, E, E, T, E, T, E, F, T, E, F, E], [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 (And.intro z_151 trivial))

theorem z_153 : le (tf [F, E, E, E, E, F, E, E, T, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, E, E, T, F] [([F, E, E, E, E, F, E, E, T, E, T, E, E, T, F], [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 trivial)

theorem z_154 : le (tf [F, E, E, E, E, E, F, E, T, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, E, E, T, E, F] [([F, E, E, E, E, E, F, E, T, E, T, E, T, E, F], [F, E, E, E, E, E, F, E, T, E, T, E, T, F, E]), ([F, E, E, E, E, E, F, E, T, T, E, E, E, T, F], [F, E, E, E, E, F, E, E, T, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_153 trivial))

theorem z_155 : le (tf [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E] [([F, E, F, E, E, E, E, E, E, T, F, E, T, T, E], [F, F, E, E, E, E, E, E, E, T, F, E, T, T, E]), ([F, E, F, E, E, E, E, E, E, T, F, T, E, E, T], [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_128 trivial))

theorem z_156 : le (tf [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E] [([F, E, F, E, E, E, E, E, E, T, E, T, F, T, E], [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E]), ([F, E, F, E, E, E, E, E, E, T, T, E, F, E, T], [F, F, E, E, E, E, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 (And.intro z_129 trivial))

theorem z_157 : le (tf [F, E, F, E, E, E, E, E, T, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, E, T, F, T, E] [([F, E, F, E, E, E, E, E, E, T, E, T, F, T, E], [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E]), ([F, E, F, E, E, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 (And.intro z_131 trivial))

theorem z_158 : le (tf [F, E, F, E, E, E, E, E, T, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, T, E, E, T, F] [([F, E, F, E, E, E, E, E, E, T, T, E, E, T, F], [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E]), ([F, E, F, E, E, E, E, E, T, E, E, T, E, T, F], [F, E, F, E, E, E, E, E, T, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_156 (And.intro z_157 trivial))

theorem z_159 : le (tf [F, E, E, F, E, E, E, E, T, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, E, E, E, T, F] [([F, E, E, F, E, E, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, E, E, T, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 trivial)

theorem z_160 : le (tf [F, F, E, E, E, E, E, T, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, E, E, F, T, T] [([F, F, E, E, E, E, E, E, T, E, E, E, F, T, T], [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 trivial)

theorem z_161 : le (tf [F, E, F, E, E, E, E, T, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, E, T, F, E, T] [([F, E, F, E, E, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T]), ([F, E, F, E, E, E, E, T, E, E, E, E, F, T, T], [F, F, E, E, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_160 trivial))

theorem z_162 : le (tf [F, E, E, F, E, E, E, T, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, E, T, F, T, E] [([F, E, E, F, E, E, E, E, T, E, E, T, F, T, E], [F, E, F, E, E, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, F, E, E, E, T, E, E, E, T, F, E, T], [F, E, F, E, E, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_157 (And.intro z_161 trivial))

theorem z_163 : le (tf [F, E, E, F, E, E, E, T, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, T, E, E, T, F] [([F, E, E, F, E, E, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, E, E, T, E, T, E, E, T, F]), ([F, E, E, F, E, E, E, T, E, E, E, T, E, T, F], [F, E, E, F, E, E, E, T, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 (And.intro z_162 trivial))

theorem z_164 : le (tf [F, E, E, E, F, E, E, T, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, E, E, T, F] [([F, E, E, E, F, E, E, E, T, T, E, E, E, T, F], [F, E, E, F, E, E, E, E, T, T, E, E, E, T, F]), ([F, E, E, E, F, E, E, T, E, E, T, E, E, T, F], [F, E, E, F, E, E, E, T, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_159 (And.intro z_163 trivial))

theorem z_165 : le (tf [F, E, F, E, E, E, T, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, E, E, F, T, T] [([F, E, F, E, E, E, E, T, E, E, E, E, F, T, T], [F, F, E, E, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_160 trivial)

theorem z_166 : le (tf [F, E, E, F, E, E, T, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, E, T, F, E, T] [([F, E, E, F, E, E, E, T, E, E, E, T, F, E, T], [F, E, F, E, E, E, E, T, E, E, E, T, F, E, T]), ([F, E, E, F, E, E, T, E, E, E, E, E, F, T, T], [F, E, F, E, E, E, T, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_161 (And.intro z_165 trivial))

theorem z_167 : le (tf [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E] [([F, E, E, E, F, E, E, T, E, E, E, T, F, T, E], [F, E, E, F, E, E, E, T, E, E, E, T, F, T, E]), ([F, E, E, E, F, E, T, E, E, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_162 (And.intro z_166 trivial))

theorem z_168 : le (tf [F, E, E, E, F, E, T, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, T, E, E, T, F] [([F, E, E, E, F, E, E, T, E, E, T, E, E, T, F], [F, E, E, F, E, E, E, T, E, E, T, E, E, T, F]), ([F, E, E, E, F, E, T, E, E, E, E, T, E, T, F], [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 (And.intro z_167 trivial))

theorem z_169 : le (tf [F, E, E, E, E, F, T, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, E, E, E, T, F] [([F, E, E, E, E, F, E, T, E, T, E, E, E, T, F], [F, E, E, E, F, E, E, T, E, T, E, E, E, T, F]), ([F, E, E, E, E, F, T, E, E, E, T, E, E, T, F], [F, E, E, E, F, E, T, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_168 trivial))

theorem z_170 : le (tf [F, E, E, E, E, E, T, F, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, E, E, T, E, F] [([F, E, E, E, E, E, E, F, T, T, E, E, T, E, F], [F, E, E, E, E, E, F, E, T, T, E, E, T, E, F]), ([F, E, E, E, E, E, T, F, E, E, T, E, T, E, F], [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E]), ([F, E, E, E, E, E, T, F, E, T, E, E, E, T, F], [F, E, E, E, E, F, T, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_154 (And.intro z_84 (And.intro z_169 trivial)))

theorem z_171 : le (tf [F, E, E, E, E, F, E, E, T, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, E, F, E, T] [([F, E, E, E, E, F, E, E, T, E, T, E, F, E, T], [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 trivial)

theorem z_172 : le (tf [F, E, E, E, E, E, F, E, T, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, E, E, F, T, E] [([F, E, E, E, E, E, F, E, T, E, T, E, F, T, E], [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E]), ([F, E, E, E, E, E, F, E, T, T, E, E, F, E, T], [F, E, E, E, E, F, E, E, T, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_23 (And.intro z_171 trivial))

theorem z_173 : le (tf [F, E, F, E, E, E, E, E, T, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, T, E, F, E, T] [([F, E, F, E, E, E, E, E, E, T, T, E, F, E, T], [F, F, E, E, E, E, E, E, E, T, T, E, F, E, T]), ([F, E, F, E, E, E, E, E, T, E, E, T, F, E, T], [F, F, E, E, E, E, E, E, T, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_131 trivial))

theorem z_174 : le (tf [F, E, E, F, E, E, E, E, T, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, T, E, F, T, E] [([F, E, E, F, E, E, E, E, E, T, T, E, F, T, E], [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E]), ([F, E, E, F, E, E, E, E, T, E, E, T, F, T, E], [F, E, F, E, E, E, E, E, T, E, E, T, F, T, E]), ([F, E, E, F, E, E, E, E, T, E, T, E, F, E, T], [F, E, F, E, E, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_156 (And.intro z_157 (And.intro z_173 trivial)))

theorem z_175 : le (tf [F, E, E, F, E, E, E, T, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, T, E, F, E, T] [([F, E, E, F, E, E, E, E, T, E, T, E, F, E, T], [F, E, F, E, E, E, E, E, T, E, T, E, F, E, T]), ([F, E, E, F, E, E, E, T, E, E, E, T, F, E, T], [F, E, F, E, E, E, E, T, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_173 (And.intro z_161 trivial))

theorem z_176 : le (tf [F, E, E, E, F, E, E, T, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, T, E, F, T, E] [([F, E, E, E, F, E, E, E, T, E, T, E, F, T, E], [F, E, E, F, E, E, E, E, T, E, T, E, F, T, E]), ([F, E, E, E, F, E, E, T, E, E, E, T, F, T, E], [F, E, E, F, E, E, E, T, E, E, E, T, F, T, E]), ([F, E, E, E, F, E, E, T, E, E, T, E, F, E, T], [F, E, E, F, E, E, E, T, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_174 (And.intro z_162 (And.intro z_175 trivial)))

theorem z_177 : le (tf [F, E, E, E, F, E, T, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, T, E, F, E, T] [([F, E, E, E, F, E, E, T, E, E, T, E, F, E, T], [F, E, E, F, E, E, E, T, E, E, T, E, F, E, T]), ([F, E, E, E, F, E, T, E, E, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_175 (And.intro z_166 trivial))

theorem z_178 : le (tf [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E] [([F, E, E, E, E, F, E, T, E, E, T, E, F, T, E], [F, E, E, E, F, E, E, T, E, E, T, E, F, T, E]), ([F, E, E, E, E, F, T, E, E, E, E, T, F, T, E], [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E]), ([F, E, E, E, E, F, T, E, E, E, T, E, F, E, T], [F, E, E, E, F, E, T, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_176 (And.intro z_167 (And.intro z_177 trivial)))

theorem z_179 : le (tf [F, E, E, F, E, E, E, E, T, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, E, E, F, E, T] [([F, E, E, F, E, E, E, E, T, E, T, E, F, E, T], [F, E, F, E, E, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_173 trivial)

theorem z_180 : le (tf [F, E, E, E, F, E, E, T, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, E, F, E, T] [([F, E, E, E, F, E, E, E, T, T, E, E, F, E, T], [F, E, E, F, E, E, E, E, T, T, E, E, F, E, T]), ([F, E, E, E, F, E, E, T, E, E, T, E, F, E, T], [F, E, E, F, E, E, E, T, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_179 (And.intro z_175 trivial))

theorem z_181 : le (tf [F, E, E, E, E, F, T, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, E, E, F, E, T] [([F, E, E, E, E, F, E, T, E, T, E, E, F, E, T], [F, E, E, E, F, E, E, T, E, T, E, E, F, E, T]), ([F, E, E, E, E, F, T, E, E, E, T, E, F, E, T], [F, E, E, E, F, E, T, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_180 (And.intro z_177 trivial))

theorem z_182 : le (tf [F, E, E, E, E, E, T, F, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, E, E, F, T, E] [([F, E, E, E, E, E, E, F, T, T, E, E, F, T, E], [F, E, E, E, E, E, F, E, T, T, E, E, F, T, E]), ([F, E, E, E, E, E, T, F, E, E, T, E, F, T, E], [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E]), ([F, E, E, E, E, E, T, F, E, T, E, E, F, E, T], [F, E, E, E, E, F, T, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_172 (And.intro z_178 (And.intro z_181 trivial)))

theorem z_183 : le (tf [F, E, E, E, E, E, F, E, T, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, E, F, E, E, T] [([F, E, E, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, E, E, F, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 trivial)

theorem z_184 : le (tf [F, E, F, E, E, E, E, E, E, T, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, T, F, E, E, T] [([F, E, F, E, E, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 trivial)

theorem z_185 : le (tf [F, E, F, E, E, E, E, E, T, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, E, F, T, E, T] [([F, E, F, E, E, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T]), ([F, E, F, E, E, E, E, E, T, E, E, F, E, T, T], [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 (And.intro z_130 trivial))

theorem z_186 : le (tf [F, E, E, F, E, E, E, E, T, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, T, F, E, E, T] [([F, E, E, F, E, E, E, E, E, T, T, F, E, E, T], [F, E, F, E, E, E, E, E, E, T, T, F, E, E, T]), ([F, E, E, F, E, E, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_184 (And.intro z_185 trivial))

theorem z_187 : le (tf [F, E, F, E, E, E, E, T, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, E, F, E, T, T] [([F, E, F, E, E, E, E, E, T, E, E, F, E, T, T], [F, F, E, E, E, E, E, E, T, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 trivial)

theorem z_188 : le (tf [F, E, E, F, E, E, E, T, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, E, F, T, E, T] [([F, E, E, F, E, E, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, E, E, T, E, E, F, T, E, T]), ([F, E, E, F, E, E, E, T, E, E, E, F, E, T, T], [F, E, F, E, E, E, E, T, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_185 (And.intro z_187 trivial))

theorem z_189 : le (tf [F, E, E, E, F, E, E, T, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, T, F, E, E, T] [([F, E, E, E, F, E, E, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, E, E, T, E, T, F, E, E, T]), ([F, E, E, E, F, E, E, T, E, E, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_186 (And.intro z_188 trivial))

theorem z_190 : le (tf [F, E, E, F, E, E, T, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, E, F, E, T, T] [([F, E, E, F, E, E, E, T, E, E, E, F, E, T, T], [F, E, F, E, E, E, E, T, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_187 trivial)

theorem z_191 : le (tf [F, E, E, E, F, E, T, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, E, F, T, E, T] [([F, E, E, E, F, E, E, T, E, E, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, E, E, F, T, E, T]), ([F, E, E, E, F, E, T, E, E, E, E, F, E, T, T], [F, E, E, F, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_190 trivial))

theorem z_192 : le (tf [F, E, E, E, E, F, T, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, F, E, E, T] [([F, E, E, E, E, F, E, T, E, E, T, F, E, E, T], [F, E, E, E, F, E, E, T, E, E, T, F, E, E, T]), ([F, E, E, E, E, F, T, E, E, E, E, F, T, E, T], [F, E, E, E, F, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_189 (And.intro z_191 trivial))

theorem z_193 : le (tf [F, E, E, E, E, E, T, F, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, E, F, E, E, T] [([F, E, E, E, E, E, E, F, T, T, E, F, E, E, T], [F, E, E, E, E, E, F, E, T, T, E, F, E, E, T]), ([F, E, E, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, E, F, T, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_183 (And.intro z_192 trivial))

theorem z_194 : le (tf [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T] [([F, E, E, E, E, E, T, E, F, T, E, F, E, E, T], [F, E, E, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_193 trivial)

theorem z_195 : le (tf [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E] [([F, E, E, E, E, E, T, E, F, T, E, E, F, T, E], [F, E, E, E, E, E, T, F, E, T, E, E, F, T, E]), ([F, E, E, E, E, E, T, T, F, E, E, E, F, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_182 (And.intro z_194 trivial))

theorem z_196 : le (tf [F, E, E, E, E, E, T, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, E, E, T, E, F] [([F, E, E, E, E, E, T, E, F, T, E, E, T, E, F], [F, E, E, E, E, E, T, F, E, T, E, E, T, E, F]), ([F, E, E, E, E, E, T, T, F, E, E, E, E, T, F], [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_170 (And.intro z_195 trivial))

theorem z_197 : le (tf [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F] [([F, E, E, E, E, E, T, E, T, F, E, T, E, E, F], [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E]), ([F, E, E, E, E, E, T, T, E, F, E, E, T, E, F], [F, E, E, E, E, E, T, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_151 (And.intro z_196 trivial))

theorem z_198 : le (tf [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F] [([F, E, E, E, E, E, T, E, T, T, F, E, E, E, F], [F, E, E, E, E, E, T, E, T, T, F, E, E, F, E]), ([F, E, E, E, E, E, T, T, E, E, F, T, E, E, F], [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_152 (And.intro z_197 trivial))

theorem z_199 : le (tf [F, E, E, E, E, E, T, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, T, E, E, F, E, E, F] [([F, E, E, E, E, E, T, T, E, T, E, F, E, E, F], [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 trivial)

theorem z_200 : le (tf [F, E, E, E, E, F, E, T, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, E, T, T, E, F] [([F, E, E, E, E, F, E, E, T, E, E, T, T, E, F], [F, E, E, E, E, F, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, E, F, E, T, E, E, E, T, E, T, F], [F, E, E, E, E, F, E, T, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_62 (And.intro z_26 trivial))

theorem z_201 : le (tf [F, E, E, F, E, T, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, E, E, F, T, T] [([F, E, E, F, E, E, T, E, E, E, E, E, F, T, T], [F, E, F, E, E, E, T, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 trivial)

theorem z_202 : le (tf [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T] [([F, E, E, E, F, E, T, E, E, E, E, T, F, E, T], [F, E, E, F, E, E, T, E, E, E, E, T, F, E, T]), ([F, E, E, E, F, T, E, E, E, E, E, E, F, T, T], [F, E, E, F, E, T, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_201 trivial))

theorem z_203 : le (tf [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E] [([F, E, E, E, E, E, F, T, E, E, E, T, F, T, E], [F, E, E, E, E, F, E, T, E, E, E, T, F, T, E]), ([F, E, E, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 (And.intro z_202 trivial))

theorem z_204 : le (tf [F, E, E, E, E, T, F, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, E, T, T, E, F] [([F, E, E, E, E, E, F, T, E, E, E, T, T, E, F], [F, E, E, E, E, F, E, T, E, E, E, T, T, E, F]), ([F, E, E, E, E, T, F, E, E, E, E, T, E, T, F], [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 (And.intro z_203 trivial))

theorem z_205 : le (tf [F, E, E, E, E, T, F, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, T, E, E, T, F] [([F, E, E, E, E, E, F, T, E, E, T, E, E, T, F], [F, E, E, E, E, E, F, T, E, E, T, E, F, T, E]), ([F, E, E, E, E, T, F, E, E, E, E, T, E, T, F], [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_28 (And.intro z_203 trivial))

theorem z_206 : le (tf [F, E, E, E, E, T, E, F, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, E, T, E, F] [([F, E, E, E, E, E, T, F, E, E, T, E, T, E, F], [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E]), ([F, E, E, E, E, T, E, F, E, E, E, T, T, E, F], [F, E, E, E, E, T, F, E, E, E, E, T, T, E, F]), ([F, E, E, E, E, T, E, F, E, E, T, E, E, T, F], [F, E, E, E, E, T, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_204 (And.intro z_205 trivial)))

theorem z_207 : le (tf [F, E, E, E, E, T, E, E, F, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, E, T, T, E, E, F] [([F, E, E, E, E, E, T, E, F, E, T, T, E, E, F], [F, E, E, E, E, E, T, E, F, E, T, T, E, F, E]), ([F, E, E, E, E, T, E, E, F, E, T, E, T, E, F], [F, E, E, E, E, T, E, F, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_85 (And.intro z_206 trivial))

theorem z_208 : le (tf [F, F, E, E, E, E, E, E, E, E, T, F, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, T, F, T, T, E] [([F, F, E, E, E, E, E, E, E, E, T, F, T, E, T], [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 trivial)

theorem z_209 : le (tf [F, E, F, E, E, E, E, E, E, T, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, E, F, T, T, E] [([F, E, F, E, E, E, E, E, E, E, T, F, T, T, E], [F, F, E, E, E, E, E, E, E, E, T, F, T, T, E]), ([F, E, F, E, E, E, E, E, E, T, E, F, T, E, T], [F, F, E, E, E, E, E, E, E, T, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_208 (And.intro z_77 trivial))

theorem z_210 : le (tf [F, E, E, F, E, E, E, E, E, T, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, T, F, E, T, E] [([F, E, E, F, E, E, E, E, E, T, E, F, T, T, E], [F, E, F, E, E, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, F, E, E, E, E, E, T, T, F, E, E, T], [F, E, F, E, E, E, E, E, E, T, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_184 trivial))

theorem z_211 : le (tf [F, E, E, F, E, E, E, E, T, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, E, F, T, T, E] [([F, E, E, F, E, E, E, E, E, T, E, F, T, T, E], [F, E, F, E, E, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, F, E, E, E, E, T, E, E, F, T, E, T], [F, E, F, E, E, E, E, E, T, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_185 trivial))

theorem z_212 : le (tf [F, E, E, E, F, E, E, E, T, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, T, F, E, T, E] [([F, E, E, E, F, E, E, E, E, T, T, F, E, T, E], [F, E, E, F, E, E, E, E, E, T, T, F, E, T, E]), ([F, E, E, E, F, E, E, E, T, E, E, F, T, T, E], [F, E, E, F, E, E, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, F, E, E, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_211 (And.intro z_186 trivial)))

theorem z_213 : le (tf [F, E, E, E, F, E, E, T, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, E, F, T, T, E] [([F, E, E, E, F, E, E, E, T, E, E, F, T, T, E], [F, E, E, F, E, E, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, F, E, E, T, E, E, E, F, T, E, T], [F, E, E, F, E, E, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_211 (And.intro z_188 trivial))

theorem z_214 : le (tf [F, E, E, E, E, F, E, T, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, T, F, E, T, E] [([F, E, E, E, E, F, E, E, T, E, T, F, E, T, E], [F, E, E, E, F, E, E, E, T, E, T, F, E, T, E]), ([F, E, E, E, E, F, E, T, E, E, E, F, T, T, E], [F, E, E, E, F, E, E, T, E, E, E, F, T, T, E]), ([F, E, E, E, E, F, E, T, E, E, T, F, E, E, T], [F, E, E, E, F, E, E, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_212 (And.intro z_213 (And.intro z_189 trivial)))

theorem z_215 : le (tf [F, E, F, E, E, T, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, E, E, F, E, T, T] [([F, E, F, E, E, E, T, E, E, E, E, F, E, T, T], [F, F, E, E, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_138 trivial)

theorem z_216 : le (tf [F, E, E, F, E, T, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, E, F, T, E, T] [([F, E, E, F, E, E, T, E, E, E, E, F, T, E, T], [F, E, F, E, E, E, T, E, E, E, E, F, T, E, T]), ([F, E, E, F, E, T, E, E, E, E, E, F, E, T, T], [F, E, F, E, E, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_139 (And.intro z_215 trivial))

theorem z_217 : le (tf [F, E, E, E, F, T, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, E, F, T, T, E] [([F, E, E, E, F, E, T, E, E, E, E, F, T, T, E], [F, E, E, F, E, E, T, E, E, E, E, F, T, T, E]), ([F, E, E, E, F, T, E, E, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 (And.intro z_216 trivial))

theorem z_218 : le (tf [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T] [([F, E, E, E, F, E, T, E, E, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T]), ([F, E, E, E, F, T, E, E, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_141 (And.intro z_216 trivial))

theorem z_219 : le (tf [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E] [([F, E, E, E, E, E, F, T, E, E, T, F, E, T, E], [F, E, E, E, E, F, E, T, E, E, T, F, E, T, E]), ([F, E, E, E, E, T, F, E, E, E, E, F, T, T, E], [F, E, E, E, F, T, E, E, E, E, E, F, T, T, E]), ([F, E, E, E, E, T, F, E, E, E, T, F, E, E, T], [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_214 (And.intro z_217 (And.intro z_218 trivial)))

theorem z_220 : le (tf [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E] [([F, E, E, E, E, E, T, F, E, E, T, F, T, E, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]), ([F, E, E, E, E, T, E, F, E, E, T, F, E, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_143 (And.intro z_219 trivial))

theorem z_221 : le (tf [F, E, E, E, E, F, E, T, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, E, E, F, T] [([F, E, E, E, E, F, E, E, T, T, E, E, E, F, T], [F, E, E, E, E, F, E, E, T, T, E, E, F, E, T]), ([F, E, E, E, E, F, E, T, E, E, T, E, E, F, T], [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_171 (And.intro z_27 trivial))

theorem z_222 : le (tf [F, E, E, E, F, T, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, T, E, E, F, T] [([F, E, E, E, F, E, T, E, E, E, T, E, E, F, T], [F, E, E, F, E, E, T, E, E, E, T, E, E, F, T]), ([F, E, E, E, F, T, E, E, E, E, E, T, E, F, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 (And.intro z_202 trivial))

theorem z_223 : le (tf [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T] [([F, E, E, E, E, E, F, T, E, T, E, E, E, F, T], [F, E, E, E, E, F, E, T, E, T, E, E, E, F, T]), ([F, E, E, E, E, T, F, E, E, E, T, E, E, F, T], [F, E, E, E, F, T, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_221 (And.intro z_222 trivial))

theorem z_224 : le (tf [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E] [([F, E, E, E, E, E, T, F, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]), ([F, E, E, E, E, T, E, F, E, E, T, E, T, F, E], [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, E, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 (And.intro z_220 (And.intro z_223 trivial)))

theorem z_225 : le (tf [F, E, E, E, E, F, E, T, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, E, E, T, F] [([F, E, E, E, E, F, E, T, E, T, E, E, E, T, F], [F, E, E, E, F, E, E, T, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 trivial)

theorem z_226 : le (tf [F, E, F, E, E, E, E, T, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, T, E, E, F, E, T] [([F, E, F, E, E, E, E, E, T, T, E, E, F, E, T], [F, E, F, E, E, E, E, E, T, T, E, F, E, E, T]), ([F, E, F, E, E, E, E, T, E, E, T, E, F, E, T], [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_112 (And.intro z_125 trivial))

theorem z_227 : le (tf [F, E, E, F, E, E, E, T, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, E, E, F, T, E] [([F, E, E, F, E, E, E, E, T, T, E, E, F, T, E], [F, E, E, F, E, E, E, E, T, T, E, F, E, T, E]), ([F, E, E, F, E, E, E, T, E, E, T, E, F, T, E], [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E]), ([F, E, E, F, E, E, E, T, E, T, E, E, F, E, T], [F, E, F, E, E, E, E, T, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_113 (And.intro z_126 (And.intro z_226 trivial)))

theorem z_228 : le (tf [F, F, E, E, E, F, E, E, E, E, E, T, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, F, E, E, E, E, E, T, T, T, E] [([F, F, E, E, E, F, E, E, E, E, E, T, T, E, T], [F, F, E, E, F, E, E, E, E, E, E, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 trivial)

theorem z_229 : le (tf [F, F, E, E, E, E, F, E, E, E, T, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, T, E, T, T, E] [([F, F, E, E, E, E, F, E, E, E, E, T, T, T, E], [F, F, E, E, E, F, E, E, E, E, E, T, T, T, E]), ([F, F, E, E, E, E, F, E, E, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_100 trivial))

theorem z_230 : le (tf [F, F, E, E, E, E, F, E, E, E, T, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, F, E, E, E, T, T, E, E, T] [([F, F, E, E, E, E, F, E, E, E, T, E, T, E, T], [F, F, E, E, E, F, E, E, E, E, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 trivial)

theorem z_231 : le (tf [F, F, E, E, E, E, E, F, E, E, T, T, E, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, E, T, T, E, T, E] [([F, F, E, E, E, E, E, F, E, E, T, E, T, T, E], [F, F, E, E, E, E, F, E, E, E, T, E, T, T, E]), ([F, F, E, E, E, E, E, F, E, E, T, T, E, E, T], [F, F, E, E, E, E, F, E, E, E, T, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_229 (And.intro z_230 trivial))

theorem z_232 : le (tf [F, F, E, E, E, E, E, F, E, T, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, T, E, E, T, T, E] [([F, F, E, E, E, E, E, F, E, E, T, E, T, T, E], [F, F, E, E, E, E, F, E, E, E, T, E, T, T, E]), ([F, F, E, E, E, E, E, F, E, T, E, E, T, E, T], [F, F, E, E, E, E, F, E, E, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_229 (And.intro z_102 trivial))

theorem z_233 : le (tf [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T] [([F, F, E, E, E, E, E, F, E, E, T, T, E, E, T], [F, F, E, E, E, E, F, E, E, E, T, T, E, E, T]), ([F, F, E, E, E, E, E, F, E, T, E, E, T, E, T], [F, F, E, E, E, E, F, E, E, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 (And.intro z_102 trivial))

theorem z_234 : le (tf [F, F, E, E, E, E, E, E, F, T, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, F, T, E, T, E, T, E] [([F, F, E, E, E, E, E, E, F, E, T, T, E, T, E], [F, F, E, E, E, E, E, F, E, E, T, T, E, T, E]), ([F, F, E, E, E, E, E, E, F, T, E, E, T, T, E], [F, F, E, E, E, E, E, F, E, T, E, E, T, T, E]), ([F, F, E, E, E, E, E, E, F, T, E, T, E, E, T], [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_232 (And.intro z_233 trivial)))

theorem z_235 : le (tf [F, F, E, E, E, E, E, E, T, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, E, F, T, E, T, E] [([F, F, E, E, E, E, E, E, E, T, F, T, E, T, E], [F, F, E, E, E, E, E, E, F, T, E, T, E, T, E]), ([F, F, E, E, E, E, E, E, T, E, F, E, T, T, E], [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E]), ([F, F, E, E, E, E, E, E, T, E, F, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_234 (And.intro z_105 (And.intro z_106 trivial)))

theorem z_236 : le (tf [F, F, E, E, E, E, E, T, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, F, E, E, E, E, T, T] [([F, F, E, E, E, E, E, E, F, T, E, E, E, T, T], [F, F, E, E, E, E, E, F, E, T, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_116 trivial)

theorem z_237 : le (tf [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T] [([F, F, E, E, E, E, E, E, T, F, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T]), ([F, F, E, E, E, E, E, T, E, F, E, E, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_236 trivial))

theorem z_238 : le (tf [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T] [([F, F, E, E, E, E, E, E, T, E, F, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T]), ([F, F, E, E, E, E, E, T, E, E, F, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_237 trivial))

theorem z_239 : le (tf [F, F, E, E, E, E, E, T, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, E, T, F, T, E] [([F, F, E, E, E, E, E, E, T, E, E, T, F, T, E], [F, F, E, E, E, E, E, E, T, E, F, T, E, T, E]), ([F, F, E, E, E, E, E, T, E, E, E, T, F, E, T], [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_235 (And.intro z_238 trivial))

theorem z_240 : le (tf [F, F, E, E, E, E, T, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, E, E, T, F, E, T] [([F, F, E, E, E, E, E, T, E, E, E, T, F, E, T], [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T]), ([F, F, E, E, E, E, T, E, E, E, E, E, F, T, T], [F, F, E, E, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_238 (And.intro z_138 trivial))

theorem z_241 : le (tf [F, E, F, E, E, E, T, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, E, T, F, T, E] [([F, E, F, E, E, E, E, T, E, E, E, T, F, T, E], [F, F, E, E, E, E, E, T, E, E, E, T, F, T, E]), ([F, E, F, E, E, E, T, E, E, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_239 (And.intro z_240 trivial))

theorem z_242 : le (tf [F, E, E, F, E, E, T, E, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, T, E, F, T, E] [([F, E, E, F, E, E, E, T, E, E, T, E, F, T, E], [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E]), ([F, E, E, F, E, E, T, E, E, E, E, T, F, T, E], [F, E, F, E, E, E, T, E, E, E, E, T, F, T, E]), ([F, E, E, F, E, E, T, E, E, E, T, E, F, E, T], [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 (And.intro z_241 (And.intro z_141 trivial)))

theorem z_243 : le (tf [F, E, E, F, E, E, T, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, T, E, E, E, T, F] [([F, E, E, F, E, E, E, T, E, T, E, E, E, T, F], [F, E, E, F, E, E, E, T, E, T, E, E, F, T, E]), ([F, E, E, F, E, E, T, E, E, E, T, E, E, T, F], [F, E, E, F, E, E, T, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_242 trivial))

theorem z_244 : le (tf [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T] [([F, E, F, E, E, E, T, E, E, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, E, E, T, F, E, T]), ([F, E, F, E, E, T, E, E, E, E, E, E, F, T, T], [F, E, F, E, E, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_240 (And.intro z_215 trivial))

theorem z_245 : le (tf [F, E, E, F, E, T, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, E, T, F, T, E] [([F, E, E, F, E, E, T, E, E, E, E, T, F, T, E], [F, E, F, E, E, E, T, E, E, E, E, T, F, T, E]), ([F, E, E, F, E, T, E, E, E, E, E, T, F, E, T], [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_241 (And.intro z_244 trivial))

theorem z_246 : le (tf [F, E, E, F, E, T, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, T, E, E, T, F] [([F, E, E, F, E, E, T, E, E, E, T, E, E, T, F], [F, E, E, F, E, E, T, E, E, E, T, E, F, T, E]), ([F, E, E, F, E, T, E, E, E, E, E, T, E, T, F], [F, E, E, F, E, T, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_242 (And.intro z_245 trivial))

theorem z_247 : le (tf [F, E, E, E, F, T, E, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, T, E, E, E, T, F] [([F, E, E, E, F, E, T, E, E, T, E, E, E, T, F], [F, E, E, F, E, E, T, E, E, T, E, E, E, T, F]), ([F, E, E, E, F, T, E, E, E, E, T, E, E, T, F], [F, E, E, F, E, T, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_243 (And.intro z_246 trivial))

theorem z_248 : le (tf [F, E, E, E, E, T, F, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, E, E, T, F] [([F, E, E, E, E, E, F, T, T, E, E, E, E, T, F], [F, E, E, E, E, F, E, T, T, E, E, E, E, T, F]), ([F, E, E, E, E, T, F, E, E, T, E, E, E, T, F], [F, E, E, E, F, T, E, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_225 (And.intro z_247 trivial))

theorem z_249 : le (tf [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F] [([F, E, E, E, E, E, T, F, T, E, E, E, T, E, F], [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E]), ([F, E, E, E, E, T, E, F, E, T, E, E, T, E, F], [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E]), ([F, E, E, E, E, T, E, F, T, E, E, E, E, T, F], [F, E, E, E, E, T, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 (And.intro z_224 (And.intro z_248 trivial)))

theorem z_250 : le (tf [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F] [([F, E, E, E, E, E, T, E, T, F, E, T, E, E, F], [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E]), ([F, E, E, E, E, T, E, E, E, F, T, T, E, E, F], [F, E, E, E, E, T, E, E, F, E, T, T, E, E, F]), ([F, E, E, E, E, T, E, E, T, F, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_151 (And.intro z_207 (And.intro z_249 trivial)))

theorem z_251 : le (tf [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F] [([F, E, E, E, E, E, T, E, T, T, F, E, E, E, F], [F, E, E, E, E, E, T, E, T, T, F, E, E, F, E]), ([F, E, E, E, E, T, E, E, T, E, F, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_152 (And.intro z_250 trivial))

theorem z_252 : le (tf [F, E, F, E, E, E, E, E, E, T, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, T, E, T, E, F] [([F, E, F, E, E, E, E, E, E, T, E, T, T, E, F], [F, E, F, E, E, E, E, E, E, T, E, T, T, F, E]), ([F, E, F, E, E, E, E, E, E, T, T, E, E, T, F], [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_156 trivial))

theorem z_253 : le (tf [F, E, E, F, E, E, E, E, E, T, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, T, T, E, E, F] [([F, E, E, F, E, E, E, E, E, T, T, E, T, E, F], [F, E, F, E, E, E, E, E, E, T, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_252 trivial)

theorem z_254 : le (tf [F, E, E, F, E, E, E, E, T, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, T, E, T, E, F] [([F, E, E, F, E, E, E, E, E, T, T, E, T, E, F], [F, E, F, E, E, E, E, E, E, T, T, E, T, E, F]), ([F, E, E, F, E, E, E, E, T, E, E, T, T, E, F], [F, E, E, F, E, E, E, E, T, E, E, T, T, F, E]), ([F, E, E, F, E, E, E, E, T, E, T, E, E, T, F], [F, E, F, E, E, E, E, E, T, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_252 (And.intro z_67 (And.intro z_158 trivial)))

theorem z_255 : le (tf [F, E, E, E, F, E, E, E, T, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, T, T, E, E, F] [([F, E, E, E, F, E, E, E, E, T, T, T, E, E, F], [F, E, E, F, E, E, E, E, E, T, T, T, E, E, F]), ([F, E, E, E, F, E, E, E, T, E, T, E, T, E, F], [F, E, E, F, E, E, E, E, T, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_253 (And.intro z_254 trivial))

theorem z_256 : le (tf [F, E, E, E, F, E, E, E, T, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, E, E, T, E, F] [([F, E, E, E, F, E, E, E, T, E, T, E, T, E, F], [F, E, E, F, E, E, E, E, T, E, T, E, T, E, F]), ([F, E, E, E, F, E, E, E, T, T, E, E, E, T, F], [F, E, E, F, E, E, E, E, T, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_254 (And.intro z_159 trivial))

theorem z_257 : le (tf [F, E, E, E, E, F, E, E, T, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, T, E, E, F] [([F, E, E, E, E, F, E, E, T, E, T, T, E, E, F], [F, E, E, E, F, E, E, E, T, E, T, T, E, E, F]), ([F, E, E, E, E, F, E, E, T, T, E, E, T, E, F], [F, E, E, E, F, E, E, E, T, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_255 (And.intro z_256 trivial))

theorem z_258 : le (tf [F, E, E, E, E, E, F, E, T, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, T, E, E, E, F] [([F, E, E, E, E, E, F, E, T, T, E, T, E, E, F], [F, E, E, E, E, F, E, E, T, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_257 trivial)

theorem z_259 : le (tf [F, E, E, F, E, E, E, E, E, T, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, T, T, F, E, E] [([F, E, E, F, E, E, E, E, E, T, T, E, F, T, E], [F, E, F, E, E, E, E, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_156 trivial)

theorem z_260 : le (tf [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E] [([F, E, E, E, F, E, E, E, E, T, T, T, F, E, E], [F, E, E, F, E, E, E, E, E, T, T, T, F, E, E]), ([F, E, E, E, F, E, E, E, T, E, T, E, F, T, E], [F, E, E, F, E, E, E, E, T, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_259 (And.intro z_174 trivial))

theorem z_261 : le (tf [F, E, E, E, F, E, E, E, T, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, E, T, E, F, E] [([F, E, E, E, F, E, E, E, T, E, T, T, E, F, E], [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E]), ([F, E, E, E, F, E, E, E, T, T, E, E, T, F, E], [F, E, E, E, F, E, E, E, T, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_114 trivial))

theorem z_262 : le (tf [F, E, E, E, F, E, E, T, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, T, T, E, F, E] [([F, E, E, E, F, E, E, E, T, E, T, T, E, F, E], [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E]), ([F, E, E, E, F, E, E, T, E, E, T, E, T, F, E], [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_127 trivial))

theorem z_263 : le (tf [F, E, E, E, F, E, E, T, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, T, E, E, F] [([F, E, E, E, F, E, E, E, T, T, E, T, E, E, F], [F, E, E, E, F, E, E, E, T, T, E, T, E, F, E]), ([F, E, E, E, F, E, E, T, E, E, T, T, E, E, F], [F, E, E, E, F, E, E, T, E, E, T, T, E, F, E]), ([F, E, E, E, F, E, E, T, E, T, E, E, T, E, F], [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 (And.intro z_262 (And.intro z_137 trivial)))

theorem z_264 : le (tf [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E] [([F, E, E, E, E, F, E, T, E, E, T, T, E, F, E], [F, E, E, E, F, E, E, T, E, E, T, T, E, F, E]), ([F, E, E, E, E, F, T, E, E, E, T, E, T, F, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_262 (And.intro z_143 trivial))

theorem z_265 : le (tf [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F] [([F, E, E, E, E, F, E, T, E, T, E, T, E, E, F], [F, E, E, E, F, E, E, T, E, T, E, T, E, E, F]), ([F, E, E, E, E, F, T, E, E, E, T, T, E, E, F], [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]), ([F, E, E, E, E, F, T, E, E, T, E, E, T, E, F], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_264 (And.intro z_147 trivial)))

theorem z_266 : le (tf [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F] [([F, E, E, E, E, E, E, F, T, T, T, E, E, E, F], [F, E, E, E, E, E, F, E, T, T, T, E, E, E, F]), ([F, E, E, E, E, E, T, F, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_258 (And.intro z_265 trivial))

theorem z_267 : le (tf [F, E, E, F, E, E, E, E, E, T, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, T, E, T, F, E] [([F, E, E, F, E, E, E, E, E, T, E, T, T, F, E], [F, E, F, E, E, E, E, E, E, T, E, T, T, F, E]), ([F, E, E, F, E, E, E, E, E, T, T, E, E, F, T], [F, E, E, F, E, E, E, E, E, T, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_17 trivial))

theorem z_268 : le (tf [F, E, E, E, F, E, E, E, E, T, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, T, T, E, F, E] [([F, E, E, E, F, E, E, E, E, T, T, E, T, F, E], [F, E, E, F, E, E, E, E, E, T, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_267 trivial)

theorem z_269 : le (tf [F, E, E, E, F, E, E, E, T, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, T, E, T, F, E] [([F, E, E, E, F, E, E, E, E, T, T, E, T, F, E], [F, E, E, F, E, E, E, E, E, T, T, E, T, F, E]), ([F, E, E, E, F, E, E, E, T, E, E, T, T, F, E], [F, E, E, F, E, E, E, E, T, E, E, T, T, F, E]), ([F, E, E, E, F, E, E, E, T, E, T, E, E, F, T], [F, E, E, E, F, E, E, E, T, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_267 (And.intro z_67 (And.intro z_22 trivial)))

theorem z_270 : le (tf [F, E, E, E, E, F, E, E, T, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, T, T, E, F, E] [([F, E, E, E, E, F, E, E, E, T, T, T, E, F, E], [F, E, E, E, F, E, E, E, E, T, T, T, E, F, E]), ([F, E, E, E, E, F, E, E, T, E, T, E, T, F, E], [F, E, E, E, F, E, E, E, T, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_268 (And.intro z_269 trivial))

theorem z_271 : le (tf [F, E, E, E, E, F, E, E, T, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, E, T, F, E] [([F, E, E, E, E, F, E, E, T, E, T, E, T, F, E], [F, E, E, E, F, E, E, E, T, E, T, E, T, F, E]), ([F, E, E, E, E, F, E, E, T, T, E, E, E, F, T], [F, E, E, E, E, F, E, E, T, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 (And.intro z_171 trivial))

theorem z_272 : le (tf [F, E, E, E, E, E, F, E, T, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, E, T, E, F, E] [([F, E, E, E, E, E, F, E, T, E, T, T, E, F, E], [F, E, E, E, E, F, E, E, T, E, T, T, E, F, E]), ([F, E, E, E, E, E, F, E, T, T, E, E, T, F, E], [F, E, E, E, E, F, E, E, T, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_271 trivial))

theorem z_273 : le (tf [F, E, E, E, E, E, T, F, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, E, T, E, F, E] [([F, E, E, E, E, E, E, F, T, T, E, T, E, F, E], [F, E, E, E, E, E, F, E, T, T, E, T, E, F, E]), ([F, E, E, E, E, E, T, F, E, E, T, T, E, F, E], [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]), ([F, E, E, E, E, E, T, F, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_272 (And.intro z_264 (And.intro z_147 trivial)))

theorem z_274 : le (tf [F, E, E, E, F, E, E, E, E, T, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, T, F, T, E, E] [([F, E, E, E, F, E, E, E, E, T, T, F, E, T, E], [F, E, E, F, E, E, E, E, E, T, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 trivial)

theorem z_275 : le (tf [F, E, E, E, E, F, E, E, T, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, T, F, T, E, E] [([F, E, E, E, E, F, E, E, E, T, T, F, T, E, E], [F, E, E, E, F, E, E, E, E, T, T, F, T, E, E]), ([F, E, E, E, E, F, E, E, T, E, T, F, E, T, E], [F, E, E, E, F, E, E, E, T, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_274 (And.intro z_212 trivial))

theorem z_276 : le (tf [F, E, E, E, F, E, E, E, T, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, E, F, E, E, T] [([F, E, E, E, F, E, E, E, T, E, T, F, E, E, T], [F, E, E, F, E, E, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_186 trivial)

theorem z_277 : le (tf [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E] [([F, E, E, E, E, F, E, E, T, E, T, F, E, T, E], [F, E, E, E, F, E, E, E, T, E, T, F, E, T, E]), ([F, E, E, E, E, F, E, E, T, T, E, F, E, E, T], [F, E, E, E, F, E, E, E, T, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_212 (And.intro z_276 trivial))

theorem z_278 : le (tf [F, E, E, E, E, E, F, E, T, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, E, F, T, E, E] [([F, E, E, E, E, E, F, E, T, E, T, F, T, E, E], [F, E, E, E, E, F, E, E, T, E, T, F, T, E, E]), ([F, E, E, E, E, E, F, E, T, T, E, F, E, T, E], [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_275 (And.intro z_277 trivial))

theorem z_279 : le (tf [F, E, E, F, E, E, E, T, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, E, F, E, E, T] [([F, E, E, F, E, E, E, E, T, T, E, F, E, E, T], [F, E, F, E, E, E, E, E, T, T, E, F, E, E, T]), ([F, E, E, F, E, E, E, T, E, E, T, F, E, E, T], [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_112 (And.intro z_125 trivial))

theorem z_280 : le (tf [F, E, E, E, F, E, E, T, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, E, F, E, T, E] [([F, E, E, E, F, E, E, E, T, T, E, F, E, T, E], [F, E, E, F, E, E, E, E, T, T, E, F, E, T, E]), ([F, E, E, E, F, E, E, T, E, E, T, F, E, T, E], [F, E, E, F, E, E, E, T, E, E, T, F, E, T, E]), ([F, E, E, E, F, E, E, T, E, T, E, F, E, E, T], [F, E, E, F, E, E, E, T, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_113 (And.intro z_126 (And.intro z_279 trivial)))

theorem z_281 : le (tf [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T] [([F, E, E, E, F, E, E, T, E, T, E, F, E, E, T], [F, E, E, F, E, E, E, T, E, T, E, F, E, E, T]), ([F, E, E, E, F, E, T, E, E, E, T, F, E, E, T], [F, E, E, F, E, E, T, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 (And.intro z_141 trivial))

theorem z_282 : le (tf [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E] [([F, E, E, E, E, F, E, T, E, T, E, F, E, T, E], [F, E, E, E, F, E, E, T, E, T, E, F, E, T, E]), ([F, E, E, E, E, F, T, E, E, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, E, E, T, F, E, T, E]), ([F, E, E, E, E, F, T, E, E, T, E, F, E, E, T], [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 (And.intro z_142 (And.intro z_281 trivial)))

theorem z_283 : le (tf [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E] [([F, E, E, E, E, E, E, F, T, T, E, F, T, E, E], [F, E, E, E, E, E, F, E, T, T, E, F, T, E, E]), ([F, E, E, E, E, E, T, F, E, E, T, F, T, E, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]), ([F, E, E, E, E, E, T, F, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_278 (And.intro z_143 (And.intro z_282 trivial)))

theorem z_284 : le (tf [F, F, E, E, E, E, E, E, E, E, F, T, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, E, E, F, T, T, E, T] [([F, F, E, E, E, E, E, E, E, E, F, T, E, T, T], [F, F, E, E, E, E, E, E, E, F, E, T, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 trivial)

theorem z_285 : le (tf [F, E, F, E, E, E, E, E, E, E, F, T, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, F, T, T, T, E] [([F, E, F, E, E, E, E, E, E, E, F, T, T, E, T], [F, F, E, E, E, E, E, E, E, E, F, T, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 trivial)

theorem z_286 : le (tf [F, E, F, E, E, E, E, E, E, T, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, T, F, E, T, E, T] [([F, E, F, E, E, E, E, E, E, E, F, T, T, E, T], [F, F, E, E, E, E, E, E, E, E, F, T, T, E, T]), ([F, E, F, E, E, E, E, E, E, T, F, E, E, T, T], [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 (And.intro z_76 trivial))

theorem z_287 : le (tf [F, E, E, F, E, E, E, E, E, T, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, F, E, T, T, E] [([F, E, E, F, E, E, E, E, E, E, F, T, T, T, E], [F, E, F, E, E, E, E, E, E, E, F, T, T, T, E]), ([F, E, E, F, E, E, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, E, E, T, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_285 (And.intro z_286 trivial))

theorem z_288 : le (tf [F, E, E, F, E, E, E, E, E, T, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, F, T, E, E, T] [([F, E, E, F, E, E, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, E, E, T, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 trivial)

theorem z_289 : le (tf [F, E, E, E, F, E, E, E, E, T, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, T, F, T, E, T, E] [([F, E, E, E, F, E, E, E, E, T, F, E, T, T, E], [F, E, E, F, E, E, E, E, E, T, F, E, T, T, E]), ([F, E, E, E, F, E, E, E, E, T, F, T, E, E, T], [F, E, E, F, E, E, E, E, E, T, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_288 trivial))

theorem z_290 : le (tf [F, E, F, E, E, E, E, E, T, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, F, E, E, T, T] [([F, E, F, E, E, E, E, E, E, T, F, E, E, T, T], [F, F, E, E, E, E, E, E, E, T, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 trivial)

theorem z_291 : le (tf [F, E, E, F, E, E, E, E, T, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, F, E, T, E, T] [([F, E, E, F, E, E, E, E, E, T, F, E, T, E, T], [F, E, F, E, E, E, E, E, E, T, F, E, T, E, T]), ([F, E, E, F, E, E, E, E, T, E, F, E, E, T, T], [F, E, F, E, E, E, E, E, T, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 (And.intro z_290 trivial))

theorem z_292 : le (tf [F, E, E, E, F, E, E, E, T, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, F, E, T, T, E] [([F, E, E, E, F, E, E, E, E, T, F, E, T, T, E], [F, E, E, F, E, E, E, E, E, T, F, E, T, T, E]), ([F, E, E, E, F, E, E, E, T, E, F, E, T, E, T], [F, E, E, F, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_291 trivial))

theorem z_293 : le (tf [F, E, E, E, F, E, E, E, T, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, F, T, E, E, T] [([F, E, E, E, F, E, E, E, E, T, F, T, E, E, T], [F, E, E, F, E, E, E, E, E, T, F, T, E, E, T]), ([F, E, E, E, F, E, E, E, T, E, F, E, T, E, T], [F, E, E, F, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_288 (And.intro z_291 trivial))

theorem z_294 : le (tf [F, E, E, E, E, F, E, E, T, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, E, F, T, E, T, E] [([F, E, E, E, E, F, E, E, E, T, F, T, E, T, E], [F, E, E, E, F, E, E, E, E, T, F, T, E, T, E]), ([F, E, E, E, E, F, E, E, T, E, F, E, T, T, E], [F, E, E, E, F, E, E, E, T, E, F, E, T, T, E]), ([F, E, E, E, E, F, E, E, T, E, F, T, E, E, T], [F, E, E, E, F, E, E, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_289 (And.intro z_292 (And.intro z_293 trivial)))

theorem z_295 : le (tf [F, E, E, E, E, F, E, E, T, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, F, E, E, E, T] [([F, E, E, E, E, F, E, E, T, E, F, T, E, E, T], [F, E, E, E, F, E, E, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_293 trivial)

theorem z_296 : le (tf [F, E, E, E, E, E, F, E, T, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, F, E, E, T, E] [([F, E, E, E, E, E, F, E, T, E, F, T, E, T, E], [F, E, E, E, E, F, E, E, T, E, F, T, E, T, E]), ([F, E, E, E, E, E, F, E, T, T, F, E, E, E, T], [F, E, E, E, E, F, E, E, T, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_294 (And.intro z_295 trivial))

theorem z_297 : le (tf [F, E, F, E, E, E, E, E, T, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, F, E, T, T, E] [([F, E, F, E, E, E, E, E, E, T, F, E, T, T, E], [F, F, E, E, E, E, E, E, E, T, F, E, T, T, E]), ([F, E, F, E, E, E, E, E, T, E, F, E, T, E, T], [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_120 trivial))

theorem z_298 : le (tf [F, E, F, E, E, E, E, E, T, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, E, F, T, E, E, T] [([F, E, F, E, E, E, E, E, E, T, F, T, E, E, T], [F, F, E, E, E, E, E, E, E, T, F, T, E, E, T]), ([F, E, F, E, E, E, E, E, T, E, F, E, T, E, T], [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 (And.intro z_120 trivial))

theorem z_299 : le (tf [F, E, E, F, E, E, E, E, T, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, E, F, T, E, T, E] [([F, E, E, F, E, E, E, E, E, T, F, T, E, T, E], [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E]), ([F, E, E, F, E, E, E, E, T, E, F, E, T, T, E], [F, E, F, E, E, E, E, E, T, E, F, E, T, T, E]), ([F, E, E, F, E, E, E, E, T, E, F, T, E, E, T], [F, E, F, E, E, E, E, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 (And.intro z_297 (And.intro z_298 trivial)))

theorem z_300 : le (tf [F, E, F, E, E, E, E, T, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, F, E, T, E, T] [([F, E, F, E, E, E, E, E, T, E, F, E, T, E, T], [F, F, E, E, E, E, E, E, T, E, F, E, T, E, T]), ([F, E, F, E, E, E, E, T, E, E, F, E, E, T, T], [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_120 (And.intro z_122 trivial))

theorem z_301 : le (tf [F, E, E, F, E, E, E, T, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, F, E, T, T, E] [([F, E, E, F, E, E, E, E, T, E, F, E, T, T, E], [F, E, F, E, E, E, E, E, T, E, F, E, T, T, E]), ([F, E, E, F, E, E, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_297 (And.intro z_300 trivial))

theorem z_302 : le (tf [F, E, E, F, E, E, E, T, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, F, T, E, E, T] [([F, E, E, F, E, E, E, E, T, E, F, T, E, E, T], [F, E, F, E, E, E, E, E, T, E, F, T, E, E, T]), ([F, E, E, F, E, E, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_298 (And.intro z_300 trivial))

theorem z_303 : le (tf [F, E, E, E, F, E, E, T, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, F, T, E, T, E] [([F, E, E, E, F, E, E, E, T, E, F, T, E, T, E], [F, E, E, F, E, E, E, E, T, E, F, T, E, T, E]), ([F, E, E, E, F, E, E, T, E, E, F, E, T, T, E], [F, E, E, F, E, E, E, T, E, E, F, E, T, T, E]), ([F, E, E, E, F, E, E, T, E, E, F, T, E, E, T], [F, E, E, F, E, E, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 (And.intro z_301 (And.intro z_302 trivial)))

theorem z_304 : le (tf [F, E, F, E, E, E, T, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, F, E, E, T, T] [([F, E, F, E, E, E, E, T, E, E, F, E, E, T, T], [F, F, E, E, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_122 trivial)

theorem z_305 : le (tf [F, E, E, F, E, E, T, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, F, E, T, E, T] [([F, E, E, F, E, E, E, T, E, E, F, E, T, E, T], [F, E, F, E, E, E, E, T, E, E, F, E, T, E, T]), ([F, E, E, F, E, E, T, E, E, E, F, E, E, T, T], [F, E, F, E, E, E, T, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_300 (And.intro z_304 trivial))

theorem z_306 : le (tf [F, E, E, E, F, E, T, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, F, E, T, T, E] [([F, E, E, E, F, E, E, T, E, E, F, E, T, T, E], [F, E, E, F, E, E, E, T, E, E, F, E, T, T, E]), ([F, E, E, E, F, E, T, E, E, E, F, E, T, E, T], [F, E, E, F, E, E, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_301 (And.intro z_305 trivial))

theorem z_307 : le (tf [F, E, E, E, F, E, T, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, F, T, E, E, T] [([F, E, E, E, F, E, E, T, E, E, F, T, E, E, T], [F, E, E, F, E, E, E, T, E, E, F, T, E, E, T]), ([F, E, E, E, F, E, T, E, E, E, F, E, T, E, T], [F, E, E, F, E, E, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_302 (And.intro z_305 trivial))

theorem z_308 : le (tf [F, E, E, E, E, F, T, E, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, F, T, E, T, E] [([F, E, E, E, E, F, E, T, E, E, F, T, E, T, E], [F, E, E, E, F, E, E, T, E, E, F, T, E, T, E]), ([F, E, E, E, E, F, T, E, E, E, F, E, T, T, E], [F, E, E, E, F, E, T, E, E, E, F, E, T, T, E]), ([F, E, E, E, E, F, T, E, E, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_303 (And.intro z_306 (And.intro z_307 trivial)))

theorem z_309 : le (tf [F, E, E, F, E, E, E, E, T, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, F, E, E, E, T] [([F, E, E, F, E, E, E, E, T, E, F, T, E, E, T], [F, E, F, E, E, E, E, E, T, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_298 trivial)

theorem z_310 : le (tf [F, E, E, E, F, E, E, T, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, F, E, E, E, T] [([F, E, E, E, F, E, E, E, T, T, F, E, E, E, T], [F, E, E, F, E, E, E, E, T, T, F, E, E, E, T]), ([F, E, E, E, F, E, E, T, E, E, F, T, E, E, T], [F, E, E, F, E, E, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 (And.intro z_302 trivial))

theorem z_311 : le (tf [F, E, E, E, E, F, T, E, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, F, E, E, E, T] [([F, E, E, E, E, F, E, T, E, T, F, E, E, E, T], [F, E, E, E, F, E, E, T, E, T, F, E, E, E, T]), ([F, E, E, E, E, F, T, E, E, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_310 (And.intro z_307 trivial))

theorem z_312 : le (tf [F, E, E, E, E, E, T, F, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, F, E, E, T, E] [([F, E, E, E, E, E, E, F, T, T, F, E, E, T, E], [F, E, E, E, E, E, F, E, T, T, F, E, E, T, E]), ([F, E, E, E, E, E, T, F, E, E, F, T, E, T, E], [F, E, E, E, E, F, T, E, E, E, F, T, E, T, E]), ([F, E, E, E, E, E, T, F, E, T, F, E, E, E, T], [F, E, E, E, E, F, T, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_296 (And.intro z_308 (And.intro z_311 trivial)))

theorem z_313 : le (tf [F, E, E, E, E, E, T, T, F, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, F, E, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_314 : le (tf [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E] [([F, E, E, E, E, E, T, E, F, T, F, E, E, T, E], [F, E, E, E, E, E, T, F, E, T, F, E, E, T, E]), ([F, E, E, E, E, E, T, T, F, E, F, E, E, E, T], [F, E, E, E, E, E, T, T, F, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_313 trivial))

theorem z_315 : le (tf [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E] [([F, E, E, E, E, E, T, E, F, T, E, F, T, E, E], [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E]), ([F, E, E, E, E, E, T, T, F, E, E, F, E, T, E], [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_283 (And.intro z_314 trivial))

theorem z_316 : le (tf [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E] [([F, E, E, E, E, E, T, E, F, T, E, T, E, F, E], [F, E, E, E, E, E, T, F, E, T, E, T, E, F, E]), ([F, E, E, E, E, E, T, T, F, E, E, E, T, F, E], [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_273 (And.intro z_315 trivial))

theorem z_317 : le (tf [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F] [([F, E, E, E, E, E, T, E, F, T, T, E, E, E, F], [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F]), ([F, E, E, E, E, E, T, T, F, E, E, T, E, E, F], [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_316 trivial))

theorem z_318 : le (tf [F, E, E, E, E, F, E, E, T, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, E, T, F, E, E] [([F, E, E, E, E, F, E, E, T, E, T, T, F, E, E], [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E]), ([F, E, E, E, E, F, E, E, T, T, E, E, F, T, E], [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_277 trivial))

theorem z_319 : le (tf [F, E, E, E, E, E, F, E, T, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, T, E, F, E, E] [([F, E, E, E, E, E, F, E, T, T, E, T, F, E, E], [F, E, E, E, E, F, E, E, T, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_318 trivial)

theorem z_320 : le (tf [F, E, E, F, E, E, E, E, E, T, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, T, F, T, T, E, E] [([F, E, E, F, E, E, E, E, E, T, F, T, E, T, E], [F, E, F, E, E, E, E, E, E, T, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 trivial)

theorem z_321 : le (tf [F, E, E, E, F, E, E, E, T, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, E, F, T, T, E, E] [([F, E, E, E, F, E, E, E, E, T, F, T, T, E, E], [F, E, E, F, E, E, E, E, E, T, F, T, T, E, E]), ([F, E, E, E, F, E, E, E, T, E, F, T, E, T, E], [F, E, E, F, E, E, E, E, T, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_320 (And.intro z_299 trivial))

theorem z_322 : le (tf [F, E, E, E, F, E, E, E, T, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, F, E, E, T, E] [([F, E, E, E, F, E, E, E, T, E, F, T, E, T, E], [F, E, E, F, E, E, E, E, T, E, F, T, E, T, E]), ([F, E, E, E, F, E, E, E, T, T, F, E, E, E, T], [F, E, E, F, E, E, E, E, T, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 (And.intro z_309 trivial))

theorem z_323 : le (tf [F, E, E, E, E, F, E, E, T, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, T, F, E, T, E, E] [([F, E, E, E, E, F, E, E, T, E, F, T, T, E, E], [F, E, E, E, F, E, E, E, T, E, F, T, T, E, E]), ([F, E, E, E, E, F, E, E, T, T, F, E, E, T, E], [F, E, E, E, F, E, E, E, T, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_321 (And.intro z_322 trivial))

theorem z_324 : le (tf [F, E, E, E, E, E, F, E, T, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, T, F, T, E, E, E] [([F, E, E, E, E, E, F, E, T, T, F, E, T, E, E], [F, E, E, E, E, F, E, E, T, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_323 trivial)

theorem z_325 : le (tf [F, F, E, E, E, E, E, E, T, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, E, T, T, F, E, E, E, T] [([F, F, E, E, E, E, E, E, T, E, F, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 trivial)

theorem z_326 : le (tf [F, E, F, E, E, E, E, E, T, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, T, F, E, E, T, E] [([F, E, F, E, E, E, E, E, T, E, F, T, E, T, E], [F, F, E, E, E, E, E, E, T, E, F, T, E, T, E]), ([F, E, F, E, E, E, E, E, T, T, F, E, E, E, T], [F, F, E, E, E, E, E, E, T, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_235 (And.intro z_325 trivial))

theorem z_327 : le (tf [F, E, E, F, E, E, E, E, T, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, F, E, T, E, E] [([F, E, E, F, E, E, E, E, T, E, F, T, T, E, E], [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E]), ([F, E, E, F, E, E, E, E, T, T, F, E, E, T, E], [F, E, F, E, E, E, E, E, T, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_326 trivial))

theorem z_328 : le (tf [F, F, E, E, E, E, E, T, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, E, T, E, E, F, E, T, T, E] [([F, F, E, E, E, E, E, E, T, E, F, E, T, T, E], [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E]), ([F, F, E, E, E, E, E, T, E, E, F, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_237 trivial))

theorem z_329 : le (tf [F, E, F, E, E, E, E, T, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, E, F, T, E, T, E] [([F, E, F, E, E, E, E, E, T, E, F, T, E, T, E], [F, F, E, E, E, E, E, E, T, E, F, T, E, T, E]), ([F, E, F, E, E, E, E, T, E, E, F, E, T, T, E], [F, F, E, E, E, E, E, T, E, E, F, E, T, T, E]), ([F, E, F, E, E, E, E, T, E, E, F, T, E, E, T], [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_235 (And.intro z_328 (And.intro z_238 trivial)))

theorem z_330 : le (tf [F, E, E, F, E, E, E, T, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, F, T, T, E, E] [([F, E, E, F, E, E, E, E, T, E, F, T, T, E, E], [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E]), ([F, E, E, F, E, E, E, T, E, E, F, T, E, T, E], [F, E, F, E, E, E, E, T, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_329 trivial))

theorem z_331 : le (tf [F, E, F, E, E, E, E, T, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, T, F, E, E, E, T] [([F, E, F, E, E, E, E, E, T, T, F, E, E, E, T], [F, F, E, E, E, E, E, E, T, T, F, E, E, E, T]), ([F, E, F, E, E, E, E, T, E, E, F, T, E, E, T], [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_325 (And.intro z_238 trivial))

theorem z_332 : le (tf [F, E, E, F, E, E, E, T, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, T, F, E, E, T, E] [([F, E, E, F, E, E, E, E, T, T, F, E, E, T, E], [F, E, F, E, E, E, E, E, T, T, F, E, E, T, E]), ([F, E, E, F, E, E, E, T, E, E, F, T, E, T, E], [F, E, F, E, E, E, E, T, E, E, F, T, E, T, E]), ([F, E, E, F, E, E, E, T, E, T, F, E, E, E, T], [F, E, F, E, E, E, E, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_326 (And.intro z_329 (And.intro z_331 trivial)))

theorem z_333 : le (tf [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E] [([F, E, E, E, F, E, E, E, T, T, F, E, T, E, E], [F, E, E, F, E, E, E, E, T, T, F, E, T, E, E]), ([F, E, E, E, F, E, E, T, E, E, F, T, T, E, E], [F, E, E, F, E, E, E, T, E, E, F, T, T, E, E]), ([F, E, E, E, F, E, E, T, E, T, F, E, E, T, E], [F, E, E, F, E, E, E, T, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 (And.intro z_330 (And.intro z_332 trivial)))

theorem z_334 : le (tf [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T] [([F, F, E, E, E, E, E, T, E, F, E, E, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_335 : le (tf [F, F, E, E, E, E, T, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, E, E, E, F, E, T, E, T] [([F, F, E, E, E, E, E, T, E, E, F, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T]), ([F, F, E, E, E, E, T, E, E, E, F, E, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 (And.intro z_334 trivial))

theorem z_336 : le (tf [F, E, F, E, E, E, T, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, F, E, T, T, E] [([F, E, F, E, E, E, E, T, E, E, F, E, T, T, E], [F, F, E, E, E, E, E, T, E, E, F, E, T, T, E]), ([F, E, F, E, E, E, T, E, E, E, F, E, T, E, T], [F, F, E, E, E, E, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_328 (And.intro z_335 trivial))

theorem z_337 : le (tf [F, E, F, E, E, E, T, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, F, T, E, E, T] [([F, E, F, E, E, E, E, T, E, E, F, T, E, E, T], [F, F, E, E, E, E, E, T, E, E, F, T, E, E, T]), ([F, E, F, E, E, E, T, E, E, E, F, E, T, E, T], [F, F, E, E, E, E, T, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_238 (And.intro z_335 trivial))

theorem z_338 : le (tf [F, E, E, F, E, E, T, E, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, E, F, T, E, T, E] [([F, E, E, F, E, E, E, T, E, E, F, T, E, T, E], [F, E, F, E, E, E, E, T, E, E, F, T, E, T, E]), ([F, E, E, F, E, E, T, E, E, E, F, E, T, T, E], [F, E, F, E, E, E, T, E, E, E, F, E, T, T, E]), ([F, E, E, F, E, E, T, E, E, E, F, T, E, E, T], [F, E, F, E, E, E, T, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_329 (And.intro z_336 (And.intro z_337 trivial)))

theorem z_339 : le (tf [F, E, E, E, F, E, T, E, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, F, T, T, E, E] [([F, E, E, E, F, E, E, T, E, E, F, T, T, E, E], [F, E, E, F, E, E, E, T, E, E, F, T, T, E, E]), ([F, E, E, E, F, E, T, E, E, E, F, T, E, T, E], [F, E, E, F, E, E, T, E, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 (And.intro z_338 trivial))

theorem z_340 : le (tf [F, E, E, F, E, E, T, E, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, T, F, E, E, E, T] [([F, E, E, F, E, E, E, T, E, T, F, E, E, E, T], [F, E, F, E, E, E, E, T, E, T, F, E, E, E, T]), ([F, E, E, F, E, E, T, E, E, E, F, T, E, E, T], [F, E, F, E, E, E, T, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 (And.intro z_337 trivial))

theorem z_341 : le (tf [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E] [([F, E, E, E, F, E, E, T, E, T, F, E, E, T, E], [F, E, E, F, E, E, E, T, E, T, F, E, E, T, E]), ([F, E, E, E, F, E, T, E, E, E, F, T, E, T, E], [F, E, E, F, E, E, T, E, E, E, F, T, E, T, E]), ([F, E, E, E, F, E, T, E, E, T, F, E, E, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_338 (And.intro z_340 trivial)))

theorem z_342 : le (tf [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E] [([F, E, E, E, E, F, E, T, E, T, F, E, T, E, E], [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E]), ([F, E, E, E, E, F, T, E, E, E, F, T, T, E, E], [F, E, E, E, F, E, T, E, E, E, F, T, T, E, E]), ([F, E, E, E, E, F, T, E, E, T, F, E, E, T, E], [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_339 (And.intro z_341 trivial)))

theorem z_343 : le (tf [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E] [([F, E, E, E, E, E, E, F, T, T, F, T, E, E, E], [F, E, E, E, E, E, F, E, T, T, F, T, E, E, E]), ([F, E, E, E, E, E, T, F, E, T, F, E, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_324 (And.intro z_342 trivial))

theorem z_344 : le (tf [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E] [([F, E, E, E, E, E, E, F, T, T, T, E, F, E, E], [F, E, E, E, E, E, F, E, T, T, T, E, F, E, E]), ([F, E, E, E, E, E, T, F, E, T, E, T, F, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_319 (And.intro z_343 trivial))

theorem z_345 : le (tf [F, E, E, F, E, E, E, T, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, E, E, E, F, E, T] [([F, E, E, F, E, E, E, T, E, T, E, E, F, E, T], [F, E, F, E, E, E, E, T, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 trivial)

theorem z_346 : le (tf [F, E, E, E, F, E, E, T, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, E, F, T, E] [([F, E, E, E, F, E, E, T, E, T, E, E, F, T, E], [F, E, E, F, E, E, E, T, E, T, E, E, F, T, E]), ([F, E, E, E, F, E, E, T, T, E, E, E, F, E, T], [F, E, E, F, E, E, E, T, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_345 trivial))

theorem z_347 : le (tf [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T] [([F, E, E, E, F, E, E, T, T, E, E, E, F, E, T], [F, E, E, F, E, E, E, T, T, E, E, E, F, E, T]), ([F, E, E, E, F, E, T, E, E, T, E, E, F, E, T], [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 (And.intro z_281 trivial))

theorem z_348 : le (tf [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E] [([F, E, E, E, E, F, E, T, T, E, E, E, F, T, E], [F, E, E, E, F, E, E, T, T, E, E, E, F, T, E]), ([F, E, E, E, E, F, T, E, E, T, E, E, F, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([F, E, E, E, E, F, T, E, T, E, E, E, F, E, T], [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_282 (And.intro z_347 trivial)))

theorem z_349 : le (tf [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E] [([F, E, E, E, E, E, T, F, E, T, E, T, F, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]), ([F, E, E, E, E, E, T, F, T, E, E, E, F, T, E], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_348 trivial))

theorem z_350 : le (tf [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E] [([F, E, E, E, E, E, T, F, E, T, T, E, E, F, E], [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]), ([F, E, E, E, E, E, T, F, T, E, E, T, E, F, E], [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_349 trivial))

theorem z_351 : le (tf [F, E, E, E, F, E, E, E, T, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, T, T, E, E, E, F] [([F, E, E, E, F, E, E, E, T, T, E, T, E, E, F], [F, E, E, E, F, E, E, E, T, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 trivial)

theorem z_352 : le (tf [F, E, E, E, E, F, E, T, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, T, E, E, E, F] [([F, E, E, E, E, F, E, E, T, T, T, E, E, E, F], [F, E, E, E, F, E, E, E, T, T, T, E, E, E, F]), ([F, E, E, E, E, F, E, T, E, T, E, T, E, E, F], [F, E, E, E, F, E, E, T, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_351 (And.intro z_263 trivial))

theorem z_353 : le (tf [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E] [([F, E, E, E, E, F, E, E, T, T, E, T, E, F, E], [F, E, E, E, F, E, E, E, T, T, E, T, E, F, E]), ([F, E, E, E, E, F, E, T, E, E, T, T, E, F, E], [F, E, E, E, F, E, E, T, E, E, T, T, E, F, E]), ([F, E, E, E, E, F, E, T, E, T, E, E, T, F, E], [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 (And.intro z_262 (And.intro z_137 trivial)))

theorem z_354 : le (tf [F, E, E, E, E, F, E, T, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, T, T, F, E, E] [([F, E, E, E, E, F, E, E, T, E, T, T, F, E, E], [F, E, E, E, F, E, E, E, T, E, T, T, F, E, E]), ([F, E, E, E, E, F, E, T, E, E, T, E, F, T, E], [F, E, E, E, F, E, E, T, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_176 trivial))

theorem z_355 : le (tf [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E] [([F, E, E, E, E, E, F, T, E, E, T, T, F, E, E], [F, E, E, E, E, F, E, T, E, E, T, T, F, E, E]), ([F, E, E, E, E, T, F, E, E, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_354 (And.intro z_219 trivial))

theorem z_356 : le (tf [F, E, E, E, E, F, E, T, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, F, T, E, E] [([F, E, E, E, E, F, E, E, T, T, E, F, T, E, E], [F, E, E, E, F, E, E, E, T, T, E, F, T, E, E]), ([F, E, E, E, E, F, E, T, E, E, T, F, T, E, E], [F, E, E, E, F, E, E, T, E, E, T, F, T, E, E]), ([F, E, E, E, E, F, E, T, E, T, E, F, E, T, E], [F, E, E, E, F, E, E, T, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 (And.intro z_127 (And.intro z_280 trivial)))

theorem z_357 : le (tf [F, E, F, E, E, E, E, T, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, F, E, E, T, T, E] [([F, E, F, E, E, E, E, E, T, F, E, E, T, T, E], [F, F, E, E, E, E, E, E, T, F, E, E, T, T, E]), ([F, E, F, E, E, E, E, T, E, F, E, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_237 trivial))

theorem z_358 : le (tf [F, E, F, E, E, E, E, T, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, F, E, T, E, E, T] [([F, E, F, E, E, E, E, E, T, F, E, T, E, E, T], [F, F, E, E, E, E, E, E, T, F, E, T, E, E, T]), ([F, E, F, E, E, E, E, T, E, F, E, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_237 trivial))

theorem z_359 : le (tf [F, E, E, F, E, E, E, T, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, F, E, T, E, T, E] [([F, E, E, F, E, E, E, E, T, F, E, T, E, T, E], [F, E, F, E, E, E, E, E, T, F, E, T, E, T, E]), ([F, E, E, F, E, E, E, T, E, F, E, E, T, T, E], [F, E, F, E, E, E, E, T, E, F, E, E, T, T, E]), ([F, E, E, F, E, E, E, T, E, F, E, T, E, E, T], [F, E, F, E, E, E, E, T, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_357 (And.intro z_358 trivial)))

theorem z_360 : le (tf [F, E, E, E, F, E, E, T, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, F, E, T, T, E, E] [([F, E, E, E, F, E, E, E, T, F, E, T, T, E, E], [F, E, E, F, E, E, E, E, T, F, E, T, T, E, E]), ([F, E, E, E, F, E, E, T, E, F, E, T, E, T, E], [F, E, E, F, E, E, E, T, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_359 trivial))

theorem z_361 : le (tf [F, E, E, F, E, E, E, T, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, F, T, E, E, E, T] [([F, E, E, F, E, E, E, E, T, F, T, E, E, E, T], [F, E, F, E, E, E, E, E, T, F, T, E, E, E, T]), ([F, E, E, F, E, E, E, T, E, F, E, T, E, E, T], [F, E, F, E, E, E, E, T, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 (And.intro z_358 trivial))

theorem z_362 : le (tf [F, E, E, E, F, E, E, T, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, F, T, E, E, T, E] [([F, E, E, E, F, E, E, E, T, F, T, E, E, T, E], [F, E, E, F, E, E, E, E, T, F, T, E, E, T, E]), ([F, E, E, E, F, E, E, T, E, F, E, T, E, T, E], [F, E, E, F, E, E, E, T, E, F, E, T, E, T, E]), ([F, E, E, E, F, E, E, T, E, F, T, E, E, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 (And.intro z_359 (And.intro z_361 trivial)))

theorem z_363 : le (tf [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E] [([F, E, E, E, E, F, E, E, T, F, T, E, T, E, E], [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E]), ([F, E, E, E, E, F, E, T, E, F, E, T, T, E, E], [F, E, E, E, F, E, E, T, E, F, E, T, T, E, E]), ([F, E, E, E, E, F, E, T, E, F, T, E, E, T, E], [F, E, E, E, F, E, E, T, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 (And.intro z_360 (And.intro z_362 trivial)))

theorem z_364 : le (tf [F, E, F, E, E, E, E, E, F, E, T, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, F, E, T, T, E, T, E] [([F, E, F, E, E, E, E, E, F, E, T, E, T, T, E], [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E]), ([F, E, F, E, E, E, E, E, F, E, T, T, E, E, T], [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_93 trivial))

theorem z_365 : le (tf [F, E, E, F, E, E, E, E, F, E, T, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, F, E, T, T, T, E, E] [([F, E, E, F, E, E, E, E, F, E, T, T, E, T, E], [F, E, F, E, E, E, E, E, F, E, T, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_364 trivial)

theorem z_366 : le (tf [F, E, F, E, E, E, E, E, F, T, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, F, T, E, E, T, T, E] [([F, E, F, E, E, E, E, E, F, E, T, E, T, T, E], [F, F, E, E, E, E, E, E, F, E, T, E, T, T, E]), ([F, E, F, E, E, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_117 trivial))

theorem z_367 : le (tf [F, E, F, E, E, E, E, E, F, T, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, F, T, E, T, E, E, T] [([F, E, F, E, E, E, E, E, F, E, T, T, E, E, T], [F, F, E, E, E, E, E, E, F, E, T, T, E, E, T]), ([F, E, F, E, E, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_117 trivial))

theorem z_368 : le (tf [F, E, E, F, E, E, E, E, F, T, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, F, T, E, T, E, T, E] [([F, E, E, F, E, E, E, E, F, E, T, T, E, T, E], [F, E, F, E, E, E, E, E, F, E, T, T, E, T, E]), ([F, E, E, F, E, E, E, E, F, T, E, E, T, T, E], [F, E, F, E, E, E, E, E, F, T, E, E, T, T, E]), ([F, E, E, F, E, E, E, E, F, T, E, T, E, E, T], [F, E, F, E, E, E, E, E, F, T, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_364 (And.intro z_366 (And.intro z_367 trivial)))

theorem z_369 : le (tf [F, E, E, E, F, E, E, E, F, T, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, F, T, E, T, T, E, E] [([F, E, E, E, F, E, E, E, F, E, T, T, T, E, E], [F, E, E, F, E, E, E, E, F, E, T, T, T, E, E]), ([F, E, E, E, F, E, E, E, F, T, E, T, E, T, E], [F, E, E, F, E, E, E, E, F, T, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_365 (And.intro z_368 trivial))

theorem z_370 : le (tf [F, E, F, E, E, E, E, T, F, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, F, E, E, E, T, E, T] [([F, E, F, E, E, E, E, E, F, T, E, E, T, E, T], [F, F, E, E, E, E, E, E, F, T, E, E, T, E, T]), ([F, E, F, E, E, E, E, T, F, E, E, E, E, T, T], [F, F, E, E, E, E, E, T, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 (And.intro z_236 trivial))

theorem z_371 : le (tf [F, E, E, F, E, E, E, T, F, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, F, E, E, E, T, T, E] [([F, E, E, F, E, E, E, E, F, T, E, E, T, T, E], [F, E, F, E, E, E, E, E, F, T, E, E, T, T, E]), ([F, E, E, F, E, E, E, T, F, E, E, E, T, E, T], [F, E, F, E, E, E, E, T, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_366 (And.intro z_370 trivial))

theorem z_372 : le (tf [F, E, E, F, E, E, E, T, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, F, E, E, T, E, E, T] [([F, E, E, F, E, E, E, E, F, T, E, T, E, E, T], [F, E, F, E, E, E, E, E, F, T, E, T, E, E, T]), ([F, E, E, F, E, E, E, T, F, E, E, E, T, E, T], [F, E, F, E, E, E, E, T, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 (And.intro z_370 trivial))

theorem z_373 : le (tf [F, E, E, E, F, E, E, T, F, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, F, E, E, T, E, T, E] [([F, E, E, E, F, E, E, E, F, T, E, T, E, T, E], [F, E, E, F, E, E, E, E, F, T, E, T, E, T, E]), ([F, E, E, E, F, E, E, T, F, E, E, E, T, T, E], [F, E, E, F, E, E, E, T, F, E, E, E, T, T, E]), ([F, E, E, E, F, E, E, T, F, E, E, T, E, E, T], [F, E, E, F, E, E, E, T, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 (And.intro z_371 (And.intro z_372 trivial)))

theorem z_374 : le (tf [F, E, E, E, E, F, E, T, F, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, F, E, E, T, T, E, E] [([F, E, E, E, E, F, E, E, F, T, E, T, T, E, E], [F, E, E, E, F, E, E, E, F, T, E, T, T, E, E]), ([F, E, E, E, E, F, E, T, F, E, E, T, E, T, E], [F, E, E, E, F, E, E, T, F, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 (And.intro z_373 trivial))

theorem z_375 : le (tf [F, E, F, E, E, E, E, F, E, T, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, E, T, E, T, E, T, E] [([F, E, F, E, E, E, E, F, E, E, T, T, E, T, E], [F, F, E, E, E, E, E, F, E, E, T, T, E, T, E]), ([F, E, F, E, E, E, E, F, E, T, E, E, T, T, E], [F, F, E, E, E, E, E, F, E, T, E, E, T, T, E]), ([F, E, F, E, E, E, E, F, E, T, E, T, E, E, T], [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 (And.intro z_232 (And.intro z_233 trivial)))

theorem z_376 : le (tf [F, E, F, E, E, E, E, F, T, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, T, E, E, E, T, T, E] [([F, E, F, E, E, E, E, F, E, T, E, E, T, T, E], [F, F, E, E, E, E, E, F, E, T, E, E, T, T, E]), ([F, E, F, E, E, E, E, F, T, E, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_232 (And.intro z_104 trivial))

theorem z_377 : le (tf [F, E, F, E, E, E, E, F, T, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, T, E, E, T, E, E, T] [([F, E, F, E, E, E, E, F, E, T, E, T, E, E, T], [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T]), ([F, E, F, E, E, E, E, F, T, E, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_233 (And.intro z_104 trivial))

theorem z_378 : le (tf [F, E, E, F, E, E, E, F, T, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, F, T, E, E, T, E, T, E] [([F, E, E, F, E, E, E, F, E, T, E, T, E, T, E], [F, E, F, E, E, E, E, F, E, T, E, T, E, T, E]), ([F, E, E, F, E, E, E, F, T, E, E, E, T, T, E], [F, E, F, E, E, E, E, F, T, E, E, E, T, T, E]), ([F, E, E, F, E, E, E, F, T, E, E, T, E, E, T], [F, E, F, E, E, E, E, F, T, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_375 (And.intro z_376 (And.intro z_377 trivial)))

theorem z_379 : le (tf [F, F, E, E, E, E, T, F, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, E, T, F, E, E, E, E, E, T, T] [([F, F, E, E, E, E, E, F, T, E, E, E, E, T, T], [F, F, E, E, E, E, F, E, T, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 trivial)

theorem z_380 : le (tf [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T] [([F, E, F, E, E, E, E, F, T, E, E, E, T, E, T], [F, F, E, E, E, E, E, F, T, E, E, E, T, E, T]), ([F, E, F, E, E, E, T, F, E, E, E, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_379 trivial))

theorem z_381 : le (tf [F, E, E, F, E, E, T, F, E, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, F, E, E, E, E, T, T, E] [([F, E, E, F, E, E, E, F, T, E, E, E, T, T, E], [F, E, F, E, E, E, E, F, T, E, E, E, T, T, E]), ([F, E, E, F, E, E, T, F, E, E, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_376 (And.intro z_380 trivial))

theorem z_382 : le (tf [F, E, E, F, E, E, T, F, E, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, F, E, E, E, T, E, E, T] [([F, E, E, F, E, E, E, F, T, E, E, T, E, E, T], [F, E, F, E, E, E, E, F, T, E, E, T, E, E, T]), ([F, E, E, F, E, E, T, F, E, E, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_377 (And.intro z_380 trivial))

theorem z_383 : le (tf [F, E, E, E, F, E, T, F, E, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, F, E, E, E, T, E, T, E] [([F, E, E, E, F, E, E, F, T, E, E, T, E, T, E], [F, E, E, F, E, E, E, F, T, E, E, T, E, T, E]), ([F, E, E, E, F, E, T, F, E, E, E, E, T, T, E], [F, E, E, F, E, E, T, F, E, E, E, E, T, T, E]), ([F, E, E, E, F, E, T, F, E, E, E, T, E, E, T], [F, E, E, F, E, E, T, F, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_378 (And.intro z_381 (And.intro z_382 trivial)))

theorem z_384 : le (tf [F, F, E, E, E, T, E, E, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, E, F, E, E, E, E, T, T] [([F, F, E, E, E, E, T, E, F, E, E, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_379 trivial)

theorem z_385 : le (tf [F, E, F, E, E, T, E, E, F, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, F, E, E, E, T, E, T] [([F, E, F, E, E, E, T, E, F, E, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T]), ([F, E, F, E, E, T, E, E, F, E, E, E, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_380 (And.intro z_384 trivial))

theorem z_386 : le (tf [F, E, E, F, E, T, E, E, F, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, F, E, E, E, T, T, E] [([F, E, E, F, E, E, T, E, F, E, E, E, T, T, E], [F, E, E, F, E, E, T, F, E, E, E, E, T, T, E]), ([F, E, E, F, E, T, E, E, F, E, E, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_381 (And.intro z_385 trivial))

theorem z_387 : le (tf [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T] [([F, E, E, F, E, E, T, E, F, E, E, T, E, E, T], [F, E, E, F, E, E, T, F, E, E, E, T, E, E, T]), ([F, E, E, F, E, T, E, E, F, E, E, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_382 (And.intro z_385 trivial))

theorem z_388 : le (tf [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E] [([F, E, E, E, F, E, T, E, F, E, E, T, E, T, E], [F, E, E, E, F, E, T, F, E, E, E, T, E, T, E]), ([F, E, E, E, F, T, E, E, F, E, E, E, T, T, E], [F, E, E, F, E, T, E, E, F, E, E, E, T, T, E]), ([F, E, E, E, F, T, E, E, F, E, E, T, E, E, T], [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_383 (And.intro z_386 (And.intro z_387 trivial)))

theorem z_389 : le (tf [F, E, E, E, E, T, F, E, F, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, F, E, E, T, T, E, E] [([F, E, E, E, E, E, F, T, F, E, E, T, T, E, E], [F, E, E, E, E, F, E, T, F, E, E, T, T, E, E]), ([F, E, E, E, E, T, F, E, F, E, E, T, E, T, E], [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_374 (And.intro z_388 trivial))

theorem z_390 : le (tf [F, E, E, F, E, E, E, E, F, T, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, F, T, T, E, E, E, T] [([F, E, E, F, E, E, E, E, F, T, E, T, E, E, T], [F, E, F, E, E, E, E, E, F, T, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 trivial)

theorem z_391 : le (tf [F, E, E, E, F, E, E, E, F, T, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, F, T, T, E, E, T, E] [([F, E, E, E, F, E, E, E, F, T, E, T, E, T, E], [F, E, E, F, E, E, E, E, F, T, E, T, E, T, E]), ([F, E, E, E, F, E, E, E, F, T, T, E, E, E, T], [F, E, E, F, E, E, E, E, F, T, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 (And.intro z_390 trivial))

theorem z_392 : le (tf [F, E, E, E, F, E, E, T, F, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, F, E, T, E, E, E, T] [([F, E, E, E, F, E, E, E, F, T, T, E, E, E, T], [F, E, E, F, E, E, E, E, F, T, T, E, E, E, T]), ([F, E, E, E, F, E, E, T, F, E, E, T, E, E, T], [F, E, E, F, E, E, E, T, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_390 (And.intro z_372 trivial))

theorem z_393 : le (tf [F, E, E, E, E, F, E, T, F, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, F, E, T, E, E, T, E] [([F, E, E, E, E, F, E, E, F, T, T, E, E, T, E], [F, E, E, E, F, E, E, E, F, T, T, E, E, T, E]), ([F, E, E, E, E, F, E, T, F, E, E, T, E, T, E], [F, E, E, E, F, E, E, T, F, E, E, T, E, T, E]), ([F, E, E, E, E, F, E, T, F, E, T, E, E, E, T], [F, E, E, E, F, E, E, T, F, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 (And.intro z_373 (And.intro z_392 trivial)))

theorem z_394 : le (tf [F, E, F, E, E, E, E, F, E, T, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, E, T, T, E, E, E, T] [([F, E, F, E, E, E, E, F, E, T, E, T, E, E, T], [F, F, E, E, E, E, E, F, E, T, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_233 trivial)

theorem z_395 : le (tf [F, E, E, F, E, E, E, F, T, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, F, T, E, T, E, E, E, T] [([F, E, E, F, E, E, E, F, E, T, T, E, E, E, T], [F, E, F, E, E, E, E, F, E, T, T, E, E, E, T]), ([F, E, E, F, E, E, E, F, T, E, E, T, E, E, T], [F, E, F, E, E, E, E, F, T, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_394 (And.intro z_377 trivial))

theorem z_396 : le (tf [F, E, E, E, F, E, T, F, E, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, F, E, E, T, E, E, E, T] [([F, E, E, E, F, E, E, F, T, E, T, E, E, E, T], [F, E, E, F, E, E, E, F, T, E, T, E, E, E, T]), ([F, E, E, E, F, E, T, F, E, E, E, T, E, E, T], [F, E, E, F, E, E, T, F, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_395 (And.intro z_382 trivial))

theorem z_397 : le (tf [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T] [([F, E, E, E, F, E, T, E, F, E, T, E, E, E, T], [F, E, E, E, F, E, T, F, E, E, T, E, E, E, T]), ([F, E, E, E, F, T, E, E, F, E, E, T, E, E, T], [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_396 (And.intro z_387 trivial))

theorem z_398 : le (tf [F, E, E, E, E, T, F, E, F, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, F, E, T, E, E, T, E] [([F, E, E, E, E, E, F, T, F, E, T, E, E, T, E], [F, E, E, E, E, F, E, T, F, E, T, E, E, T, E]), ([F, E, E, E, E, T, F, E, F, E, E, T, E, T, E], [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E]), ([F, E, E, E, E, T, F, E, F, E, T, E, E, E, T], [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_393 (And.intro z_388 (And.intro z_397 trivial)))

theorem z_399 : le (tf [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E] [([F, E, E, E, E, E, F, T, E, F, T, E, T, E, E], [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E]), ([F, E, E, E, E, T, F, E, E, F, E, T, T, E, E], [F, E, E, E, E, T, F, E, F, E, E, T, T, E, E]), ([F, E, E, E, E, T, F, E, E, F, T, E, E, T, E], [F, E, E, E, E, T, F, E, F, E, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_363 (And.intro z_389 (And.intro z_398 trivial)))

theorem z_400 : le (tf [F, E, E, E, E, F, E, T, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, F, E, E, T, E] [([F, E, E, E, E, F, E, E, T, T, F, E, E, T, E], [F, E, E, E, F, E, E, E, T, T, F, E, E, T, E]), ([F, E, E, E, E, F, E, T, E, E, F, T, E, T, E], [F, E, E, E, F, E, E, T, E, E, F, T, E, T, E]), ([F, E, E, E, E, F, E, T, E, T, F, E, E, E, T], [F, E, E, E, F, E, E, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_322 (And.intro z_303 (And.intro z_310 trivial)))

theorem z_401 : le (tf [F, F, E, E, E, T, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, E, T, E, E, E, E, F, E, E, T, T] [([F, F, E, E, E, E, T, E, E, E, F, E, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 trivial)

theorem z_402 : le (tf [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T] [([F, E, F, E, E, E, T, E, E, E, F, E, T, E, T], [F, F, E, E, E, E, T, E, E, E, F, E, T, E, T]), ([F, E, F, E, E, T, E, E, E, E, F, E, E, T, T], [F, F, E, E, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_401 trivial))

theorem z_403 : le (tf [F, E, E, F, E, T, E, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, F, E, T, T, E] [([F, E, E, F, E, E, T, E, E, E, F, E, T, T, E], [F, E, F, E, E, E, T, E, E, E, F, E, T, T, E]), ([F, E, E, F, E, T, E, E, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_336 (And.intro z_402 trivial))

theorem z_404 : le (tf [F, E, E, F, E, T, E, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, F, T, E, E, T] [([F, E, E, F, E, E, T, E, E, E, F, T, E, E, T], [F, E, F, E, E, E, T, E, E, E, F, T, E, E, T]), ([F, E, E, F, E, T, E, E, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_337 (And.intro z_402 trivial))

theorem z_405 : le (tf [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E] [([F, E, E, E, F, E, T, E, E, E, F, T, E, T, E], [F, E, E, F, E, E, T, E, E, E, F, T, E, T, E]), ([F, E, E, E, F, T, E, E, E, E, F, E, T, T, E], [F, E, E, F, E, T, E, E, E, E, F, E, T, T, E]), ([F, E, E, E, F, T, E, E, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_338 (And.intro z_403 (And.intro z_404 trivial)))

theorem z_406 : le (tf [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T] [([F, E, E, E, F, E, T, E, E, T, F, E, E, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, E, E, T]), ([F, E, E, E, F, T, E, E, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_340 (And.intro z_404 trivial))

theorem z_407 : le (tf [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E] [([F, E, E, E, E, E, F, T, E, T, F, E, E, T, E], [F, E, E, E, E, F, E, T, E, T, F, E, E, T, E]), ([F, E, E, E, E, T, F, E, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E]), ([F, E, E, E, E, T, F, E, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_400 (And.intro z_405 (And.intro z_406 trivial)))

theorem z_408 : le (tf [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E] [([F, E, E, E, E, E, F, T, E, T, E, F, T, E, E], [F, E, E, E, E, F, E, T, E, T, E, F, T, E, E]), ([F, E, E, E, E, T, F, E, E, E, T, F, T, E, E], [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E]), ([F, E, E, E, E, T, F, E, E, T, E, F, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_356 (And.intro z_399 (And.intro z_407 trivial)))

theorem z_409 : le (tf [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E] [([F, E, E, E, E, E, F, T, E, T, E, T, E, F, E], [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E]), ([F, E, E, E, E, T, F, E, E, E, T, T, E, F, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([F, E, E, E, E, T, F, E, E, T, E, E, T, F, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_353 (And.intro z_355 (And.intro z_408 trivial)))

theorem z_410 : le (tf [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F] [([F, E, E, E, E, E, F, T, E, T, T, E, E, E, F], [F, E, E, E, E, F, E, T, E, T, T, E, E, E, F]), ([F, E, E, E, E, T, F, E, E, T, E, T, E, E, F], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_352 (And.intro z_409 trivial))

theorem z_411 : le (tf [F, E, E, E, F, E, E, T, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, E, T, E, F] [([F, E, E, E, F, E, E, T, E, T, E, E, T, E, F], [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E]), ([F, E, E, E, F, E, E, T, T, E, E, E, E, T, F], [F, E, E, E, F, E, E, T, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 (And.intro z_346 trivial))

theorem z_412 : le (tf [F, E, E, E, E, F, E, T, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, T, E, E, F] [([F, E, E, E, E, F, E, T, E, T, E, T, E, E, F], [F, E, E, E, F, E, E, T, E, T, E, T, E, E, F]), ([F, E, E, E, E, F, E, T, T, E, E, E, T, E, F], [F, E, E, E, F, E, E, T, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_411 trivial))

theorem z_413 : le (tf [F, E, E, E, E, F, E, T, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, E, T, F, E] [([F, E, E, E, E, F, E, T, E, T, E, E, T, F, E], [F, E, E, E, F, E, E, T, E, T, E, E, T, F, E]), ([F, E, E, E, E, F, E, T, T, E, E, E, E, F, T], [F, E, E, E, F, E, E, T, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 (And.intro z_148 trivial))

theorem z_414 : le (tf [F, E, F, E, E, E, T, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, E, T, E, F, E, T] [([F, E, F, E, E, E, E, T, E, E, T, E, F, E, T], [F, E, F, E, E, E, E, T, E, E, T, F, E, E, T]), ([F, E, F, E, E, E, T, E, E, E, E, T, F, E, T], [F, F, E, E, E, E, T, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_125 (And.intro z_240 trivial))

theorem z_415 : le (tf [F, E, F, E, E, E, T, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, T, E, E, E, F, T] [([F, E, F, E, E, E, E, T, E, T, E, E, E, F, T], [F, E, F, E, E, E, E, T, E, T, E, E, F, E, T]), ([F, E, F, E, E, E, T, E, E, E, T, E, E, F, T], [F, E, F, E, E, E, T, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 (And.intro z_414 trivial))

theorem z_416 : le (tf [F, E, F, E, E, T, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, E, T, E, E, F, T] [([F, E, F, E, E, E, T, E, E, E, T, E, E, F, T], [F, E, F, E, E, E, T, E, E, E, T, E, F, E, T]), ([F, E, F, E, E, T, E, E, E, E, E, T, E, F, T], [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_414 (And.intro z_244 trivial))

theorem z_417 : le (tf [F, E, E, F, E, T, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, T, E, E, E, F, T] [([F, E, E, F, E, E, T, E, E, T, E, E, E, F, T], [F, E, F, E, E, E, T, E, E, T, E, E, E, F, T]), ([F, E, E, F, E, T, E, E, E, E, T, E, E, F, T], [F, E, F, E, E, T, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_415 (And.intro z_416 trivial))

theorem z_418 : le (tf [F, E, E, E, F, T, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, T, E, E, E, E, F, T] [([F, E, E, E, F, E, T, E, T, E, E, E, E, F, T], [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T]), ([F, E, E, E, F, T, E, E, E, T, E, E, E, F, T], [F, E, E, F, E, T, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 (And.intro z_417 trivial))

theorem z_419 : le (tf [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E] [([F, E, E, E, E, E, F, T, T, E, E, E, T, F, E], [F, E, E, E, E, F, E, T, T, E, E, E, T, F, E]), ([F, E, E, E, E, T, F, E, E, T, E, E, T, F, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]), ([F, E, E, E, E, T, F, E, T, E, E, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_408 (And.intro z_418 trivial)))

theorem z_420 : le (tf [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F] [([F, E, E, E, E, E, F, T, T, E, E, T, E, E, F], [F, E, E, E, E, F, E, T, T, E, E, T, E, E, F]), ([F, E, E, E, E, T, F, E, E, T, E, T, E, E, F], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([F, E, E, E, E, T, F, E, T, E, E, E, T, E, F], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 (And.intro z_409 (And.intro z_419 trivial)))

theorem z_421 : le (tf [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F] [([F, E, E, E, E, E, T, F, T, E, T, E, E, E, F], [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E]), ([F, E, E, E, E, T, E, F, E, T, T, E, E, E, F], [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F]), ([F, E, E, E, E, T, E, F, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_350 (And.intro z_410 (And.intro z_420 trivial)))

theorem z_422 : le (tf [F, E, E, E, E, T, E, F, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, T, E, F, E] [([F, E, E, E, E, E, T, F, E, E, T, T, E, F, E], [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]), ([F, E, E, E, E, T, E, F, E, E, T, E, T, F, E], [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_264 (And.intro z_220 trivial))

theorem z_423 : le (tf [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F] [([F, E, E, E, E, E, T, F, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F]), ([F, E, E, E, E, T, E, F, E, E, T, T, E, E, F], [F, E, E, E, E, T, E, F, E, E, T, T, E, F, E]), ([F, E, E, E, E, T, E, F, E, T, E, E, T, E, F], [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_422 (And.intro z_224 trivial)))

theorem z_424 : le (tf [F, E, E, E, F, E, E, T, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, F, E, E, T] [([F, E, E, E, F, E, E, T, E, T, E, F, E, E, T], [F, E, E, F, E, E, E, T, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 trivial)

theorem z_425 : le (tf [F, E, E, E, E, F, E, T, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, F, E, T, E] [([F, E, E, E, E, F, E, T, E, T, E, F, E, T, E], [F, E, E, E, F, E, E, T, E, T, E, F, E, T, E]), ([F, E, E, E, E, F, E, T, T, E, E, F, E, E, T], [F, E, E, E, F, E, E, T, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 (And.intro z_424 trivial))

theorem z_426 : le (tf [F, E, F, E, E, E, E, T, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, T, E, E, F, E, E, T] [([F, E, F, E, E, E, E, T, E, T, E, F, E, E, T], [F, E, F, E, E, E, E, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 trivial)

theorem z_427 : le (tf [F, E, E, F, E, E, T, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, T, E, E, F, E, E, T] [([F, E, E, F, E, E, E, T, T, E, E, F, E, E, T], [F, E, F, E, E, E, E, T, T, E, E, F, E, E, T]), ([F, E, E, F, E, E, T, E, E, T, E, F, E, E, T], [F, E, E, F, E, E, T, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_426 (And.intro z_340 trivial))

theorem z_428 : le (tf [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T] [([F, E, E, E, F, E, T, E, T, E, E, F, E, E, T], [F, E, E, F, E, E, T, E, T, E, E, F, E, E, T]), ([F, E, E, E, F, T, E, E, E, T, E, F, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_427 (And.intro z_406 trivial))

theorem z_429 : le (tf [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E] [([F, E, E, E, E, E, F, T, T, E, E, F, E, T, E], [F, E, E, E, E, F, E, T, T, E, E, F, E, T, E]), ([F, E, E, E, E, T, F, E, E, T, E, F, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E]), ([F, E, E, E, E, T, F, E, T, E, E, F, E, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_425 (And.intro z_407 (And.intro z_428 trivial)))

theorem z_430 : le (tf [F, E, E, F, E, E, T, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, T, E, E, E, E, F, E, T] [([F, E, E, F, E, E, T, E, T, E, E, E, F, E, T], [F, E, E, F, E, E, T, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_427 trivial)

theorem z_431 : le (tf [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T] [([F, E, E, E, F, E, T, T, E, E, E, E, F, E, T], [F, E, E, F, E, E, T, T, E, E, E, E, F, E, T]), ([F, E, E, E, F, T, E, E, T, E, E, E, F, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_430 (And.intro z_428 trivial))

theorem z_432 : le (tf [F, E, E, E, E, T, F, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, E, E, F, T, E] [([F, E, E, E, E, T, F, E, T, E, E, E, F, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]), ([F, E, E, E, E, T, F, T, E, E, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_431 trivial))

theorem z_433 : le (tf [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F] [([F, E, E, E, E, T, F, E, T, E, E, E, T, E, F], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([F, E, E, E, E, T, F, T, E, E, E, E, E, T, F], [F, E, E, E, E, T, F, T, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_432 trivial))

theorem z_434 : le (tf [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F] [([F, E, E, E, E, E, T, T, F, E, E, T, E, E, F], [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E]), ([F, E, E, E, E, T, E, E, F, T, E, T, E, E, F], [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F]), ([F, E, E, E, E, T, E, T, F, E, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 (And.intro z_423 (And.intro z_433 trivial)))

theorem z_435 : le (tf [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F] [([F, E, E, E, E, E, T, T, E, F, T, E, E, E, F], [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F]), ([F, E, E, E, E, T, E, E, T, F, T, E, E, E, F], [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F]), ([F, E, E, E, E, T, E, T, E, F, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 (And.intro z_421 (And.intro z_434 trivial)))

theorem z_436 : le (tf [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F] [([F, E, E, E, E, E, T, T, E, T, E, F, E, E, F], [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F]), ([F, E, E, E, E, T, E, E, T, T, E, F, E, E, F], [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F]), ([F, E, E, E, E, T, E, T, E, E, T, F, E, E, F], [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 (And.intro z_251 (And.intro z_435 trivial)))

theorem z_437 : le (tf [E, F, E, E, E, T, E, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, T, E, E, F, E, E, F] [([E, F, E, E, E, E, T, T, T, E, E, F, E, E, F], [F, E, E, E, E, E, T, T, T, E, E, F, E, E, F]), ([E, F, E, E, E, T, E, T, E, T, E, F, E, E, F], [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_199 (And.intro z_436 trivial))

theorem z_438 : le (tf [F, E, E, E, E, T, E, F, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, E, E, T, F] [([F, E, E, E, E, E, T, F, E, T, E, E, E, T, F], [F, E, E, E, E, F, T, E, E, T, E, E, E, T, F]), ([F, E, E, E, E, T, E, F, E, E, T, E, E, T, F], [F, E, E, E, E, T, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_169 (And.intro z_205 trivial))

theorem z_439 : le (tf [F, E, E, E, E, T, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, E, E, E, T, F] [([F, E, E, E, E, E, T, T, F, E, E, E, E, T, F], [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E]), ([F, E, E, E, E, T, E, E, F, T, E, E, E, T, F], [F, E, E, E, E, T, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_195 (And.intro z_438 trivial))

theorem z_440 : le (tf [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F] [([F, E, E, E, E, E, T, T, E, F, E, E, T, E, F], [F, E, E, E, E, E, T, T, F, E, E, E, T, E, F]), ([F, E, E, E, E, T, E, E, T, F, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F]), ([F, E, E, E, E, T, E, T, E, F, E, E, E, T, F], [F, E, E, E, E, T, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_196 (And.intro z_249 (And.intro z_439 trivial)))

theorem z_441 : le (tf [F, E, E, E, E, T, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, E, F, E, E, E, T, F] [([F, E, E, E, E, T, E, T, E, F, E, E, E, T, F], [F, E, E, E, E, T, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_439 trivial)

theorem z_442 : le (tf [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F] [([F, E, E, E, E, T, E, T, E, E, F, E, T, E, F], [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F]), ([F, E, E, E, E, T, T, E, E, E, F, E, E, T, F], [F, E, E, E, E, T, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_440 (And.intro z_441 trivial))

theorem z_443 : le (tf [F, E, E, E, E, T, T, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, E, E, T, F, E, E, F] [([F, E, E, E, E, T, E, T, E, E, T, F, E, E, F], [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F]), ([F, E, E, E, E, T, T, E, E, E, E, F, T, E, F], [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_435 (And.intro z_442 trivial))

theorem z_444 : le (tf [E, F, E, E, E, T, T, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, E, E, T, E, F, E, E, F] [([E, F, E, E, E, T, E, T, E, T, E, F, E, E, F], [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F]), ([E, F, E, E, E, T, T, E, E, E, T, F, E, E, F], [F, E, E, E, E, T, T, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_443 trivial))

theorem z_445 : le (tf [E, E, F, E, E, T, T, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, E, T, E, E, F, E, E, F] [([E, E, F, E, E, T, E, T, T, E, E, F, E, E, F], [E, F, E, E, E, T, E, T, T, E, E, F, E, E, F]), ([E, E, F, E, E, T, T, E, E, T, E, F, E, E, F], [E, F, E, E, E, T, T, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_444 trivial))

theorem z_446 : le (tf [E, E, E, F, E, T, T, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, T, E, E, E, F, E, E, F] [([E, E, E, F, E, T, T, E, T, E, E, F, E, E, F], [E, E, F, E, E, T, T, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 trivial)

theorem z_447 : le (tf [E, F, E, E, E, E, T, T, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, T, E, F, E, E, E, F] [([E, F, E, E, E, E, T, T, E, T, F, E, E, E, F], [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 trivial)

theorem z_448 : le (tf [F, E, E, E, E, T, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, E, F, T, E, E, F] [([F, E, E, E, E, E, T, T, E, E, F, T, E, E, F], [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F]), ([F, E, E, E, E, T, E, E, T, E, F, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F]), ([F, E, E, E, E, T, E, T, E, E, F, E, T, E, F], [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_197 (And.intro z_250 (And.intro z_440 trivial)))

theorem z_449 : le (tf [E, F, E, E, E, T, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, E, T, F, E, E, E, F] [([E, F, E, E, E, E, T, T, E, T, F, E, E, E, F], [F, E, E, E, E, E, T, T, E, T, F, E, E, E, F]), ([E, F, E, E, E, T, E, E, T, T, F, E, E, E, F], [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F]), ([E, F, E, E, E, T, E, T, E, E, F, T, E, E, F], [F, E, E, E, E, T, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 (And.intro z_251 (And.intro z_448 trivial)))

theorem z_450 : le (tf [E, E, F, E, E, T, E, T, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, T, E, F, E, E, E, F] [([E, E, F, E, E, E, T, T, T, E, F, E, E, E, F], [E, F, E, E, E, E, T, T, T, E, F, E, E, E, F]), ([E, E, F, E, E, T, E, T, E, T, F, E, E, E, F], [E, F, E, E, E, T, E, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_447 (And.intro z_449 trivial))

theorem z_451 : le (tf [E, F, E, E, E, T, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, E, E, E, F, T, E, E, F] [([E, F, E, E, E, T, E, T, E, E, F, T, E, E, F], [F, E, E, E, E, T, E, T, E, E, F, T, E, E, F]), ([E, F, E, E, E, T, T, E, E, E, F, E, T, E, F], [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_448 (And.intro z_442 trivial))

theorem z_452 : le (tf [E, E, F, E, E, T, T, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, E, E, T, F, E, E, E, F] [([E, E, F, E, E, T, E, T, E, T, F, E, E, E, F], [E, F, E, E, E, T, E, T, E, T, F, E, E, E, F]), ([E, E, F, E, E, T, T, E, E, E, F, T, E, E, F], [E, F, E, E, E, T, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_449 (And.intro z_451 trivial))

theorem z_453 : le (tf [E, E, E, F, E, T, T, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, E, T, E, F, E, E, E, F] [([E, E, E, F, E, T, E, T, T, E, F, E, E, E, F], [E, E, F, E, E, T, E, T, T, E, F, E, E, E, F]), ([E, E, E, F, E, T, T, E, E, T, F, E, E, E, F], [E, E, F, E, E, T, T, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_450 (And.intro z_452 trivial))

theorem z_454 : le (tf [F, E, E, E, E, E, E, T, T, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, T, F, T, E, E, F, E] [([F, E, E, E, E, E, E, T, T, F, E, T, E, F, E], [F, E, E, E, E, E, E, T, T, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_455 : le (tf [F, E, E, E, E, E, T, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, T, F, T, E, E, E, F] [([F, E, E, E, E, E, E, T, T, F, T, E, E, E, F], [F, E, E, E, E, E, E, T, T, F, T, E, E, F, E]), ([F, E, E, E, E, E, T, E, T, F, E, T, E, E, F], [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_454 (And.intro z_151 trivial))

theorem z_456 : le (tf [E, F, E, E, E, E, T, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, E, F, T, E, E, E, F] [([E, F, E, E, E, E, T, E, T, F, T, E, E, E, F], [F, E, E, E, E, E, T, E, T, F, T, E, E, E, F]), ([E, F, E, E, E, E, T, T, E, F, E, T, E, E, F], [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_455 (And.intro z_197 trivial))

theorem z_457 : le (tf [E, E, F, E, E, E, T, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, T, F, E, E, E, E, F] [([E, E, F, E, E, E, T, T, E, F, T, E, E, E, F], [E, F, E, E, E, E, T, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_456 trivial)

theorem z_458 : le (tf [E, F, E, E, E, T, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, T, F, T, E, E, E, F] [([E, F, E, E, E, E, T, E, T, F, T, E, E, E, F], [F, E, E, E, E, E, T, E, T, F, T, E, E, E, F]), ([E, F, E, E, E, T, E, E, T, F, E, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_455 (And.intro z_250 trivial))

theorem z_459 : le (tf [E, F, E, E, E, T, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, E, F, E, T, E, E, F] [([E, F, E, E, E, E, T, T, E, F, E, T, E, E, F], [F, E, E, E, E, E, T, T, E, F, E, T, E, E, F]), ([E, F, E, E, E, T, E, E, T, F, E, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F]), ([E, F, E, E, E, T, E, T, E, F, E, E, T, E, F], [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_197 (And.intro z_250 (And.intro z_440 trivial)))

theorem z_460 : le (tf [E, E, F, E, E, T, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, E, F, T, E, E, E, F] [([E, E, F, E, E, E, T, T, E, F, T, E, E, E, F], [E, F, E, E, E, E, T, T, E, F, T, E, E, E, F]), ([E, E, F, E, E, T, E, E, T, F, T, E, E, E, F], [E, F, E, E, E, T, E, E, T, F, T, E, E, E, F]), ([E, E, F, E, E, T, E, T, E, F, E, T, E, E, F], [E, F, E, E, E, T, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_456 (And.intro z_458 (And.intro z_459 trivial)))

theorem z_461 : le (tf [E, E, E, F, E, T, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, T, F, E, E, E, E, F] [([E, E, E, F, E, E, T, T, T, F, E, E, E, E, F], [E, E, F, E, E, E, T, T, T, F, E, E, E, E, F]), ([E, E, E, F, E, T, E, T, E, F, T, E, E, E, F], [E, E, F, E, E, T, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_457 (And.intro z_460 trivial))

theorem z_462 : le (tf [F, F, E, E, T, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, E, E, E, E, E, F, E, T, T] [([F, F, E, E, E, T, E, E, E, E, E, F, E, T, T], [F, F, E, E, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_463 : le (tf [F, E, F, E, T, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, E, E, F, T, E, T] [([F, E, F, E, E, T, E, E, E, E, E, F, T, E, T], [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T]), ([F, E, F, E, T, E, E, E, E, E, E, F, E, T, T], [F, F, E, E, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_462 trivial))

theorem z_464 : le (tf [F, E, E, F, T, E, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, E, F, T, T, E] [([F, E, E, F, E, T, E, E, E, E, E, F, T, T, E], [F, E, E, F, E, T, E, E, E, E, F, E, T, T, E]), ([F, E, E, F, T, E, E, E, E, E, E, F, T, E, T], [F, E, F, E, T, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_463 trivial))

theorem z_465 : le (tf [F, E, F, E, E, E, T, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, T, E, E, F, E, E, T, E, T] [([F, E, F, E, E, E, E, T, E, F, E, E, T, E, T], [F, F, E, E, E, E, E, T, E, F, E, E, T, E, T]), ([F, E, F, E, E, E, T, E, E, F, E, E, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 (And.intro z_334 trivial))

theorem z_466 : le (tf [F, E, E, F, E, E, T, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, F, E, T, E, E, T] [([F, E, E, F, E, E, E, T, E, F, E, T, E, E, T], [F, E, F, E, E, E, E, T, E, F, E, T, E, E, T]), ([F, E, E, F, E, E, T, E, E, F, E, E, T, E, T], [F, E, F, E, E, E, T, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_358 (And.intro z_465 trivial))

theorem z_467 : le (tf [F, E, E, E, F, E, T, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, F, T, E, E, E, T] [([F, E, E, E, F, E, E, T, E, F, T, E, E, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, E, E, T]), ([F, E, E, E, F, E, T, E, E, F, E, T, E, E, T], [F, E, E, F, E, E, T, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 (And.intro z_466 trivial))

theorem z_468 : le (tf [F, F, E, E, T, E, E, E, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, E, T, E, E, E, E, F, E, E, E, T, T] [([F, F, E, E, E, T, E, E, E, F, E, E, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_384 trivial)

theorem z_469 : le (tf [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T] [([F, E, F, E, E, T, E, E, E, F, E, E, T, E, T], [F, E, F, E, E, T, E, E, F, E, E, E, T, E, T]), ([F, E, F, E, T, E, E, E, E, F, E, E, E, T, T], [F, F, E, E, T, E, E, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_385 (And.intro z_468 trivial))

theorem z_470 : le (tf [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T] [([F, E, E, F, E, T, E, E, E, F, E, T, E, E, T], [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T]), ([F, E, E, F, T, E, E, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 (And.intro z_469 trivial))

theorem z_471 : le (tf [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T] [([F, E, E, E, E, F, T, E, E, F, T, E, E, E, T], [F, E, E, E, F, E, T, E, E, F, T, E, E, E, T]), ([F, E, E, E, T, F, E, E, E, F, E, T, E, E, T], [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_467 (And.intro z_470 trivial))

theorem z_472 : le (tf [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E] [([F, E, E, E, E, F, T, E, E, E, T, F, E, T, E], [F, E, E, E, F, E, T, E, E, E, T, F, E, T, E]), ([F, E, E, E, T, F, E, E, E, E, E, F, T, T, E], [F, E, E, F, T, E, E, E, E, E, E, F, T, T, E]), ([F, E, E, E, T, F, E, E, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_142 (And.intro z_464 (And.intro z_471 trivial)))

theorem z_473 : le (tf [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E] [([F, E, E, E, E, T, F, E, E, E, T, F, T, E, E], [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E]), ([F, E, E, E, T, E, F, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 (And.intro z_472 trivial))

theorem z_474 : le (tf [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E] [([F, E, E, E, E, T, F, E, E, E, T, T, E, F, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([F, E, E, E, T, E, F, E, E, E, T, E, T, F, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_473 trivial))

theorem z_475 : le (tf [F, E, F, E, T, E, E, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, E, E, T, E, F, T] [([F, E, F, E, E, T, E, E, E, E, E, T, E, F, T], [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T]), ([F, E, F, E, T, E, E, E, E, E, E, E, T, F, T], [F, E, F, E, T, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 (And.intro z_463 trivial))

theorem z_476 : le (tf [F, E, E, F, T, E, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, T, E, E, F, T] [([F, E, E, F, E, T, E, E, E, E, T, E, E, F, T], [F, E, F, E, E, T, E, E, E, E, T, E, E, F, T]), ([F, E, E, F, T, E, E, E, E, E, E, T, E, F, T], [F, E, F, E, T, E, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_416 (And.intro z_475 trivial))

theorem z_477 : le (tf [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T] [([F, E, E, E, E, F, T, E, E, T, E, E, E, F, T], [F, E, E, E, F, E, T, E, E, T, E, E, E, F, T]), ([F, E, E, E, T, F, E, E, E, E, T, E, E, F, T], [F, E, E, F, T, E, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_146 (And.intro z_476 trivial))

theorem z_478 : le (tf [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E] [([F, E, E, E, E, T, F, E, E, T, E, E, T, F, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]), ([F, E, E, E, T, E, F, E, E, E, T, E, T, F, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]), ([F, E, E, E, T, E, F, E, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_408 (And.intro z_473 (And.intro z_477 trivial)))

theorem z_479 : le (tf [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F] [([F, E, E, E, E, T, F, E, E, T, E, T, E, E, F], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([F, E, E, E, T, E, F, E, E, E, T, T, E, E, F], [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]), ([F, E, E, E, T, E, F, E, E, T, E, E, T, E, F], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_474 (And.intro z_478 trivial)))

theorem z_480 : le (tf [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T] [([F, E, E, E, E, F, T, E, E, T, E, F, E, E, T], [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T]), ([F, E, E, E, T, F, E, E, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 (And.intro z_471 trivial))

theorem z_481 : le (tf [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E] [([F, E, E, E, E, F, T, E, E, T, E, E, F, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([F, E, E, E, T, F, E, E, E, E, T, E, F, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]), ([F, E, E, E, T, F, E, E, E, T, E, E, F, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_472 (And.intro z_480 trivial)))

theorem z_482 : le (tf [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F] [([F, E, E, E, E, F, T, E, T, E, E, E, E, T, F], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E]), ([F, E, E, E, T, F, E, E, E, T, E, E, E, T, F], [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_481 trivial))

theorem z_483 : le (tf [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F] [([F, E, E, E, E, T, F, E, T, E, E, E, T, E, F], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([F, E, E, E, T, E, F, E, E, T, E, E, T, E, F], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]), ([F, E, E, E, T, E, F, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_478 (And.intro z_482 trivial)))

theorem z_484 : le (tf [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F] [([F, E, E, E, E, T, E, F, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F]), ([F, E, E, E, T, E, E, F, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F]), ([F, E, E, E, T, E, E, F, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 (And.intro z_479 (And.intro z_483 trivial)))

theorem z_485 : le (tf [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F] [([F, E, E, E, E, T, E, E, T, F, T, E, E, E, F], [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F]), ([F, E, E, E, T, E, E, E, T, F, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 (And.intro z_484 trivial))

theorem z_486 : le (tf [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T] [([F, E, E, F, E, T, E, E, E, E, E, F, E, T, T], [F, E, F, E, E, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_215 trivial)

theorem z_487 : le (tf [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T] [([F, E, E, E, E, F, T, E, E, E, E, F, T, E, T], [F, E, E, E, F, E, T, E, E, E, E, F, T, E, T]), ([F, E, E, E, T, F, E, E, E, E, E, F, E, T, T], [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_191 (And.intro z_486 trivial))

theorem z_488 : le (tf [F, E, E, E, T, E, F, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, E, F, T, T, E] [([F, E, E, E, E, T, F, E, E, E, E, F, T, T, E], [F, E, E, E, F, T, E, E, E, E, E, F, T, T, E]), ([F, E, E, E, T, E, F, E, E, E, E, F, T, E, T], [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_217 (And.intro z_487 trivial))

theorem z_489 : le (tf [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T] [([F, E, E, E, E, T, F, E, E, E, T, F, E, E, T], [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T]), ([F, E, E, E, T, E, F, E, E, E, E, F, T, E, T], [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_218 (And.intro z_487 trivial))

theorem z_490 : le (tf [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E] [([F, E, E, E, E, T, E, F, E, E, T, F, E, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E]), ([F, E, E, E, T, E, E, F, E, E, E, F, T, T, E], [F, E, E, E, T, E, F, E, E, E, E, F, T, T, E]), ([F, E, E, E, T, E, E, F, E, E, T, F, E, E, T], [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_219 (And.intro z_488 (And.intro z_489 trivial)))

theorem z_491 : le (tf [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E] [([F, E, E, E, E, T, E, E, F, E, T, F, T, E, E], [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E]), ([F, E, E, E, T, E, E, E, F, E, T, F, E, T, E], [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_220 (And.intro z_490 trivial))

theorem z_492 : le (tf [F, E, E, E, T, F, E, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, E, T, E, F, T] [([F, E, E, E, E, F, T, E, E, E, E, T, E, F, T], [F, E, E, E, F, E, T, E, E, E, E, T, E, F, T]), ([F, E, E, E, T, F, E, E, E, E, E, E, T, F, T], [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 (And.intro z_487 trivial))

theorem z_493 : le (tf [F, E, E, E, T, E, F, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, E, E, F, T] [([F, E, E, E, E, T, F, E, E, E, T, E, E, F, T], [F, E, E, E, F, T, E, E, E, E, T, E, E, F, T]), ([F, E, E, E, T, E, F, E, E, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_222 (And.intro z_492 trivial))

theorem z_494 : le (tf [F, E, E, E, T, E, E, F, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, E, E, F, T] [([F, E, E, E, E, T, E, F, E, T, E, E, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T]), ([F, E, E, E, T, E, E, F, E, E, T, E, E, F, T], [F, E, E, E, T, E, F, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 (And.intro z_493 trivial))

theorem z_495 : le (tf [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E] [([F, E, E, E, E, T, E, E, F, T, E, E, T, F, E], [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E]), ([F, E, E, E, T, E, E, E, F, E, T, E, T, F, E], [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E]), ([F, E, E, E, T, E, E, E, F, T, E, E, E, F, T], [F, E, E, E, T, E, E, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 (And.intro z_491 (And.intro z_494 trivial)))

theorem z_496 : le (tf [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F] [([F, E, E, E, E, T, F, T, E, E, E, E, E, T, F], [F, E, E, E, E, T, F, T, E, E, E, E, F, T, E]), ([F, E, E, E, T, E, F, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 (And.intro z_482 trivial))

theorem z_497 : le (tf [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F] [([F, E, E, E, E, T, E, T, F, E, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F]), ([F, E, E, E, T, E, E, E, F, T, E, E, T, E, F], [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E]), ([F, E, E, E, T, E, E, T, F, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 (And.intro z_495 (And.intro z_496 trivial)))

theorem z_498 : le (tf [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F] [([F, E, E, E, E, T, E, T, E, F, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F]), ([F, E, E, E, T, E, E, E, T, F, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F]), ([F, E, E, E, T, E, E, T, E, F, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_484 (And.intro z_497 trivial)))

theorem z_499 : le (tf [E, F, E, E, T, E, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, F, T, E, E, E, F] [([E, F, E, E, E, T, E, T, E, F, T, E, E, E, F], [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F]), ([E, F, E, E, T, E, E, E, T, F, T, E, E, E, F], [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F]), ([E, F, E, E, T, E, E, T, E, F, E, T, E, E, F], [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_435 (And.intro z_485 (And.intro z_498 trivial)))

theorem z_500 : le (tf [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E] [([F, E, E, E, E, T, E, E, F, E, T, T, E, F, E], [F, E, E, E, E, T, E, F, E, E, T, T, E, F, E]), ([F, E, E, E, T, E, E, E, F, E, T, E, T, F, E], [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_422 (And.intro z_491 trivial))

theorem z_501 : le (tf [F, E, E, T, E, F, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, E, F, E, T, T] [([F, E, E, E, T, F, E, E, E, E, E, F, E, T, T], [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_486 trivial)

theorem z_502 : le (tf [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T] [([F, E, E, E, T, E, F, E, E, E, E, F, T, E, T], [F, E, E, E, T, F, E, E, E, E, E, F, T, E, T]), ([F, E, E, T, E, E, F, E, E, E, E, F, E, T, T], [F, E, E, T, E, F, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_487 (And.intro z_501 trivial))

theorem z_503 : le (tf [F, E, E, T, E, E, E, F, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, E, F, T, T, E] [([F, E, E, E, T, E, E, F, E, E, E, F, T, T, E], [F, E, E, E, T, E, F, E, E, E, E, F, T, T, E]), ([F, E, E, T, E, E, E, F, E, E, E, F, T, E, T], [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_488 (And.intro z_502 trivial))

theorem z_504 : le (tf [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T] [([F, E, E, E, T, E, E, F, E, E, T, F, E, E, T], [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T]), ([F, E, E, T, E, E, E, F, E, E, E, F, T, E, T], [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_489 (And.intro z_502 trivial))

theorem z_505 : le (tf [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E] [([F, E, E, E, T, E, E, E, F, E, T, F, E, T, E], [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E]), ([F, E, E, T, E, E, E, E, F, E, E, F, T, T, E], [F, E, E, T, E, E, E, F, E, E, E, F, T, T, E]), ([F, E, E, T, E, E, E, E, F, E, T, F, E, E, T], [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_490 (And.intro z_503 (And.intro z_504 trivial)))

theorem z_506 : le (tf [F, E, E, T, E, E, E, E, E, F, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, F, T, F, T, E, E] [([F, E, E, E, T, E, E, E, E, F, T, F, T, E, E], [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E]), ([F, E, E, T, E, E, E, E, E, F, T, F, E, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_491 (And.intro z_505 trivial))

theorem z_507 : le (tf [F, E, E, T, E, E, E, E, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, F, T, T, E, F, E] [([F, E, E, E, T, E, E, E, E, F, T, T, E, F, E], [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E]), ([F, E, E, T, E, E, E, E, E, F, T, E, T, F, E], [F, E, E, T, E, E, E, E, E, F, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 (And.intro z_506 trivial))

theorem z_508 : le (tf [F, E, F, T, E, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, E, E, E, F, E, T, T] [([F, E, F, E, T, E, E, E, E, E, E, F, E, T, T], [F, F, E, E, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_462 trivial)

theorem z_509 : le (tf [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T] [([F, E, E, E, F, T, E, E, E, E, E, F, T, E, T], [F, E, E, F, E, T, E, E, E, E, E, F, T, E, T]), ([F, E, E, T, F, E, E, E, E, E, E, F, E, T, T], [F, E, F, T, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_216 (And.intro z_508 trivial))

theorem z_510 : le (tf [F, E, E, T, E, F, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, E, F, T, T, E] [([F, E, E, E, T, F, E, E, E, E, E, F, T, T, E], [F, E, E, F, T, E, E, E, E, E, E, F, T, T, E]), ([F, E, E, T, E, F, E, E, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_464 (And.intro z_509 trivial))

theorem z_511 : le (tf [F, E, E, T, E, F, E, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, T, F, E, E, T] [([F, E, E, E, T, F, E, E, E, E, T, F, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T]), ([F, E, E, T, E, F, E, E, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_471 (And.intro z_509 trivial))

theorem z_512 : le (tf [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E] [([F, E, E, E, T, E, F, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]), ([F, E, E, T, E, E, F, E, E, E, E, F, T, T, E], [F, E, E, T, E, F, E, E, E, E, E, F, T, T, E]), ([F, E, E, T, E, E, F, E, E, E, T, F, E, E, T], [F, E, E, T, E, F, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_472 (And.intro z_510 (And.intro z_511 trivial)))

theorem z_513 : le (tf [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E] [([F, E, E, E, T, E, E, F, E, E, T, F, T, E, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]), ([F, E, E, T, E, E, E, F, E, E, T, F, E, T, E], [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_473 (And.intro z_512 trivial))

theorem z_514 : le (tf [F, E, E, T, F, E, E, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, E, T, E, F, T] [([F, E, E, E, F, T, E, E, E, E, E, T, E, F, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T]), ([F, E, E, T, F, E, E, E, E, E, E, E, T, F, T], [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_509 trivial))

theorem z_515 : le (tf [F, E, E, T, E, F, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, T, E, E, F, T] [([F, E, E, E, T, F, E, E, E, E, T, E, E, F, T], [F, E, E, F, T, E, E, E, E, E, T, E, E, F, T]), ([F, E, E, T, E, F, E, E, E, E, E, T, E, F, T], [F, E, E, T, F, E, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_476 (And.intro z_514 trivial))

theorem z_516 : le (tf [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T] [([F, E, E, E, T, E, F, E, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T]), ([F, E, E, T, E, E, F, E, E, E, T, E, E, F, T], [F, E, E, T, E, F, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_477 (And.intro z_515 trivial))

theorem z_517 : le (tf [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E] [([F, E, E, E, T, E, E, F, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]), ([F, E, E, T, E, E, E, F, E, E, T, E, T, F, E], [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E]), ([F, E, E, T, E, E, E, F, E, T, E, E, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_513 (And.intro z_516 trivial)))

theorem z_518 : le (tf [F, F, E, T, E, E, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, F, E, T, E, E, E, E, E, E, F, E, E, T, T] [([F, F, E, E, T, E, E, E, E, E, F, E, E, T, T], [F, F, E, E, T, E, E, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_468 trivial)

theorem z_519 : le (tf [F, E, F, T, E, E, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, E, E, F, E, T, E, T] [([F, E, F, E, T, E, E, E, E, E, F, E, T, E, T], [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T]), ([F, E, F, T, E, E, E, E, E, E, F, E, E, T, T], [F, F, E, T, E, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_469 (And.intro z_518 trivial))

theorem z_520 : le (tf [F, E, E, T, F, E, E, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, F, T, E, E, T] [([F, E, E, E, F, T, E, E, E, E, F, T, E, E, T], [F, E, E, F, E, T, E, E, E, E, F, T, E, E, T]), ([F, E, E, T, F, E, E, E, E, E, F, E, T, E, T], [F, E, F, T, E, E, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_404 (And.intro z_519 trivial))

theorem z_521 : le (tf [F, E, E, T, F, E, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, E, T, F, T, E] [([F, E, E, E, F, T, E, E, E, E, E, T, F, T, E], [F, E, E, F, E, T, E, E, E, E, E, T, F, T, E]), ([F, E, E, T, F, E, E, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_245 (And.intro z_520 trivial))

theorem z_522 : le (tf [F, E, E, T, F, E, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, T, E, E, T, F] [([F, E, E, E, F, T, E, E, E, E, T, E, E, T, F], [F, E, E, F, E, T, E, E, E, E, T, E, E, T, F]), ([F, E, E, T, F, E, E, E, E, E, E, T, E, T, F], [F, E, E, T, F, E, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_246 (And.intro z_521 trivial))

theorem z_523 : le (tf [F, E, E, T, E, F, E, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, T, E, E, E, T, F] [([F, E, E, E, T, F, E, E, E, T, E, E, E, T, F], [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E]), ([F, E, E, T, E, F, E, E, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_481 (And.intro z_522 trivial))

theorem z_524 : le (tf [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F] [([F, E, E, E, T, E, F, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F]), ([F, E, E, T, E, E, F, E, E, T, E, E, E, T, F], [F, E, E, T, E, F, E, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_482 (And.intro z_523 trivial))

theorem z_525 : le (tf [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F] [([F, E, E, E, T, E, E, F, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F]), ([F, E, E, T, E, E, E, F, E, T, E, E, T, E, F], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E]), ([F, E, E, T, E, E, E, F, T, E, E, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 (And.intro z_517 (And.intro z_524 trivial)))

theorem z_526 : le (tf [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F] [([F, E, E, E, T, E, E, E, T, F, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F]), ([F, E, E, T, E, E, E, E, E, F, T, T, E, E, F], [F, E, E, T, E, E, E, E, E, F, T, T, E, F, E]), ([F, E, E, T, E, E, E, E, T, F, E, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 (And.intro z_507 (And.intro z_525 trivial)))

theorem z_527 : le (tf [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F] [([E, F, E, E, T, E, E, E, T, F, T, E, E, E, F], [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F]), ([E, F, E, T, E, E, E, E, T, F, E, T, E, E, F], [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_485 (And.intro z_526 trivial))

theorem z_528 : le (tf [F, E, E, F, T, E, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, E, T, F, E, T] [([F, E, E, F, E, T, E, E, E, E, E, T, F, E, T], [F, E, F, E, E, T, E, E, E, E, E, T, F, E, T]), ([F, E, E, F, T, E, E, E, E, E, E, E, F, T, T], [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 (And.intro z_486 trivial))

theorem z_529 : le (tf [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E] [([F, E, E, E, E, F, T, E, E, E, E, T, F, T, E], [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E]), ([F, E, E, E, T, F, E, E, E, E, E, T, F, E, T], [F, E, E, F, T, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 (And.intro z_528 trivial))

theorem z_530 : le (tf [F, E, E, E, T, F, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, T, E, E, T, F] [([F, E, E, E, E, F, T, E, E, E, T, E, E, T, F], [F, E, E, E, F, E, T, E, E, E, T, E, E, T, F]), ([F, E, E, E, T, F, E, E, E, E, E, T, E, T, F], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_168 (And.intro z_529 trivial))

theorem z_531 : le (tf [F, E, E, E, T, E, F, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, E, E, T, F] [([F, E, E, E, E, T, F, E, E, T, E, E, E, T, F], [F, E, E, E, F, T, E, E, E, T, E, E, E, T, F]), ([F, E, E, E, T, E, F, E, E, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_247 (And.intro z_530 trivial))

theorem z_532 : le (tf [F, E, E, T, E, F, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, E, T, F, E, T] [([F, E, E, E, T, F, E, E, E, E, E, T, F, E, T], [F, E, E, F, T, E, E, E, E, E, E, T, F, E, T]), ([F, E, E, T, E, F, E, E, E, E, E, E, F, T, T], [F, E, E, T, E, F, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_528 (And.intro z_501 trivial))

theorem z_533 : le (tf [F, E, E, T, E, E, F, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, E, T, F, T, E] [([F, E, E, E, T, E, F, E, E, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E]), ([F, E, E, T, E, E, F, E, E, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_529 (And.intro z_532 trivial))

theorem z_534 : le (tf [F, E, E, T, E, E, F, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, T, E, E, T, F] [([F, E, E, E, T, E, F, E, E, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, E, E, T, E, E, T, F]), ([F, E, E, T, E, E, F, E, E, E, E, T, E, T, F], [F, E, E, T, E, E, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_530 (And.intro z_533 trivial))

theorem z_535 : le (tf [F, E, E, T, E, E, E, F, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, E, E, T, F] [([F, E, E, E, T, E, E, F, E, T, E, E, E, T, F], [F, E, E, E, T, E, F, E, E, T, E, E, E, T, F]), ([F, E, E, T, E, E, E, F, E, E, T, E, E, T, F], [F, E, E, T, E, E, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_531 (And.intro z_534 trivial))

theorem z_536 : le (tf [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F] [([F, E, E, E, T, E, E, T, F, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F]), ([F, E, E, T, E, E, E, E, F, T, E, E, E, T, F], [F, E, E, T, E, E, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_496 (And.intro z_535 trivial))

theorem z_537 : le (tf [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F] [([F, E, E, E, T, E, E, T, E, F, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F]), ([F, E, E, T, E, E, E, E, T, F, E, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F]), ([F, E, E, T, E, E, E, T, E, F, E, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 (And.intro z_525 (And.intro z_536 trivial)))

theorem z_538 : le (tf [E, F, E, T, E, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, E, F, E, T, E, E, F] [([E, F, E, E, T, E, E, T, E, F, E, T, E, E, F], [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F]), ([E, F, E, T, E, E, E, E, T, F, E, T, E, E, F], [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F]), ([E, F, E, T, E, E, E, T, E, F, E, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_526 (And.intro z_537 trivial)))

theorem z_539 : le (tf [E, E, F, T, E, E, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, T, E, F, T, E, E, E, F] [([E, E, F, E, T, E, E, T, E, F, T, E, E, E, F], [E, F, E, E, T, E, E, T, E, F, T, E, E, E, F]), ([E, E, F, T, E, E, E, E, T, F, T, E, E, E, F], [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F]), ([E, E, F, T, E, E, E, T, E, F, E, T, E, E, F], [E, F, E, T, E, E, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_499 (And.intro z_527 (And.intro z_538 trivial)))

theorem z_540 : le (tf [E, E, E, T, F, E, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, T, F, E, E, E, E, F] [([E, E, E, E, F, T, E, T, T, F, E, E, E, E, F], [E, E, E, F, E, T, E, T, T, F, E, E, E, E, F]), ([E, E, E, T, F, E, E, T, E, F, T, E, E, E, F], [E, E, F, T, E, E, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_461 (And.intro z_539 trivial))

theorem z_541 : le (tf [E, F, E, E, E, E, T, T, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, T, E, E, E, E, F] [([E, F, E, E, E, E, T, T, F, E, T, E, E, E, F], [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 trivial)

theorem z_542 : le (tf [F, E, E, E, E, T, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, T, E, E, E, F] [([F, E, E, E, E, E, T, E, F, T, T, E, E, E, F], [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F]), ([F, E, E, E, E, T, E, E, F, T, E, T, E, E, F], [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_423 trivial))

theorem z_543 : le (tf [E, F, E, E, E, T, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, F, E, T, E, E, E, F] [([E, F, E, E, E, E, T, T, F, E, T, E, E, E, F], [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F]), ([E, F, E, E, E, T, E, E, F, T, T, E, E, E, F], [F, E, E, E, E, T, E, E, F, T, T, E, E, E, F]), ([E, F, E, E, E, T, E, T, F, E, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 (And.intro z_542 (And.intro z_434 trivial)))

theorem z_544 : le (tf [E, E, F, E, E, T, E, T, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, T, E, E, E, E, F] [([E, E, F, E, E, E, T, T, F, T, E, E, E, E, F], [E, F, E, E, E, E, T, T, F, T, E, E, E, E, F]), ([E, E, F, E, E, T, E, T, F, E, T, E, E, E, F], [E, F, E, E, E, T, E, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_541 (And.intro z_543 trivial))

theorem z_545 : le (tf [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F] [([F, E, E, E, E, T, E, F, T, E, E, E, E, T, F], [F, E, E, E, E, T, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 trivial)

theorem z_546 : le (tf [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F] [([F, E, E, E, E, T, E, T, F, E, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F]), ([F, E, E, E, E, T, T, E, F, E, E, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 (And.intro z_545 trivial))

theorem z_547 : le (tf [E, F, E, E, E, T, T, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, E, F, E, E, T, E, E, F] [([E, F, E, E, E, T, E, T, F, E, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F]), ([E, F, E, E, E, T, T, E, F, E, E, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_546 trivial))

theorem z_548 : le (tf [E, E, F, E, E, T, T, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, E, F, E, T, E, E, E, F] [([E, E, F, E, E, T, E, T, F, E, T, E, E, E, F], [E, F, E, E, E, T, E, T, F, E, T, E, E, E, F]), ([E, E, F, E, E, T, T, E, F, E, E, T, E, E, F], [E, F, E, E, E, T, T, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_543 (And.intro z_547 trivial))

theorem z_549 : le (tf [E, E, E, F, E, T, T, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, E, F, T, E, E, E, E, F] [([E, E, E, F, E, T, E, T, F, T, E, E, E, E, F], [E, E, F, E, E, T, E, T, F, T, E, E, E, E, F]), ([E, E, E, F, E, T, T, E, F, E, T, E, E, E, F], [E, E, F, E, E, T, T, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_544 (And.intro z_548 trivial))

theorem z_550 : le (tf [F, E, E, E, E, E, F, T, E, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, T, T, E, E, F, E] [([F, E, E, E, E, E, F, E, T, T, T, E, E, F, E], [F, E, E, E, E, E, F, E, T, T, T, E, F, E, E]), ([F, E, E, E, E, E, F, T, E, T, E, T, E, F, E], [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_319 (And.intro z_353 trivial))

theorem z_551 : le (tf [F, E, E, E, E, E, T, E, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, T, T, E, E, F, E] [([F, E, E, E, E, E, E, T, F, T, T, E, E, F, E], [F, E, E, E, E, E, F, T, E, T, T, E, E, F, E]), ([F, E, E, E, E, E, T, E, F, T, E, T, E, F, E], [F, E, E, E, E, E, T, F, E, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_550 (And.intro z_273 trivial))

theorem z_552 : le (tf [E, F, E, E, E, E, T, T, F, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, E, T, E, E, F, E] [([E, F, E, E, E, E, T, E, F, T, T, E, E, F, E], [F, E, E, E, E, E, T, E, F, T, T, E, E, F, E]), ([E, F, E, E, E, E, T, T, F, E, E, T, E, F, E], [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_551 (And.intro z_316 trivial))

theorem z_553 : le (tf [E, E, F, E, E, E, T, T, F, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, F, T, E, E, E, F, E] [([E, E, F, E, E, E, T, T, F, E, T, E, E, F, E], [E, F, E, E, E, E, T, T, F, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_552 trivial)

theorem z_554 : le (tf [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E] [([F, E, E, E, E, E, T, E, F, T, E, T, E, F, E], [F, E, E, E, E, E, T, F, E, T, E, T, E, F, E]), ([F, E, E, E, E, T, E, E, F, E, T, T, E, F, E], [F, E, E, E, E, T, E, F, E, E, T, T, E, F, E]), ([F, E, E, E, E, T, E, E, F, T, E, E, T, F, E], [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_273 (And.intro z_422 (And.intro z_224 trivial)))

theorem z_555 : le (tf [E, F, E, E, E, T, E, E, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, F, T, T, E, E, F, E] [([E, F, E, E, E, E, T, E, F, T, T, E, E, F, E], [F, E, E, E, E, E, T, E, F, T, T, E, E, F, E]), ([E, F, E, E, E, T, E, E, F, T, E, T, E, F, E], [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_551 (And.intro z_554 trivial))

theorem z_556 : le (tf [F, E, E, E, E, T, F, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, T, E, E, E, E, E, F, T] [([F, E, E, E, E, T, F, E, T, E, E, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_418 trivial)

theorem z_557 : le (tf [F, E, E, E, E, T, E, T, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, E, E, T, F, E] [([F, E, E, E, E, E, T, T, F, E, E, E, T, F, E], [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E]), ([F, E, E, E, E, T, E, E, F, T, E, E, T, F, E], [F, E, E, E, E, T, E, F, E, T, E, E, T, F, E]), ([F, E, E, E, E, T, E, T, F, E, E, E, E, F, T], [F, E, E, E, E, T, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_315 (And.intro z_224 (And.intro z_556 trivial)))

theorem z_558 : le (tf [E, F, E, E, E, T, E, T, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, F, E, E, T, E, F, E] [([E, F, E, E, E, E, T, T, F, E, E, T, E, F, E], [F, E, E, E, E, E, T, T, F, E, E, T, E, F, E]), ([E, F, E, E, E, T, E, E, F, T, E, T, E, F, E], [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E]), ([E, F, E, E, E, T, E, T, F, E, E, E, T, F, E], [F, E, E, E, E, T, E, T, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 (And.intro z_554 (And.intro z_557 trivial)))

theorem z_559 : le (tf [E, E, F, E, E, T, E, T, F, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, E, T, E, E, F, E] [([E, E, F, E, E, E, T, T, F, E, T, E, E, F, E], [E, F, E, E, E, E, T, T, F, E, T, E, E, F, E]), ([E, E, F, E, E, T, E, E, F, T, T, E, E, F, E], [E, F, E, E, E, T, E, E, F, T, T, E, E, F, E]), ([E, E, F, E, E, T, E, T, F, E, E, T, E, F, E], [E, F, E, E, E, T, E, T, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_552 (And.intro z_555 (And.intro z_558 trivial)))

theorem z_560 : le (tf [E, E, E, F, E, T, E, T, F, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, F, T, E, E, E, F, E] [([E, E, E, F, E, E, T, T, F, T, E, E, E, F, E], [E, E, F, E, E, E, T, T, F, T, E, E, E, F, E]), ([E, E, E, F, E, T, E, T, F, E, T, E, E, F, E], [E, E, F, E, E, T, E, T, F, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_553 (And.intro z_559 trivial))

theorem z_561 : le (tf [F, E, E, E, E, F, E, T, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, E, F, T, E] [([F, E, E, E, E, F, E, E, T, T, E, E, F, T, E], [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E]), ([F, E, E, E, E, F, E, T, E, E, T, E, F, T, E], [F, E, E, E, F, E, E, T, E, E, T, E, F, T, E]), ([F, E, E, E, E, F, E, T, E, T, E, E, F, E, T], [F, E, E, E, F, E, E, T, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_277 (And.intro z_176 (And.intro z_180 trivial)))

theorem z_562 : le (tf [F, E, E, E, E, E, F, T, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, T, E, T, F, E, E] [([F, E, E, E, E, E, F, E, T, T, E, T, F, E, E], [F, E, E, E, E, F, E, E, T, T, E, T, F, E, E]), ([F, E, E, E, E, E, F, T, E, E, T, T, F, E, E], [F, E, E, E, E, F, E, T, E, E, T, T, F, E, E]), ([F, E, E, E, E, E, F, T, E, T, E, E, F, T, E], [F, E, E, E, E, F, E, T, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_318 (And.intro z_354 (And.intro z_561 trivial)))

theorem z_563 : le (tf [F, E, E, E, E, E, E, T, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, F, T, T, E, F, E, E] [([F, E, E, E, E, E, E, T, F, T, E, T, F, E, E], [F, E, E, E, E, E, F, T, E, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 trivial)

theorem z_564 : le (tf [F, E, E, E, E, F, E, E, E, T, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, T, T, F, E, E] [([F, E, E, E, E, F, E, E, E, T, T, E, F, T, E], [F, E, E, E, F, E, E, E, E, T, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 trivial)

theorem z_565 : le (tf [F, E, E, E, E, E, F, E, T, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, E, T, T, F, E, E] [([F, E, E, E, E, E, F, E, E, T, T, T, F, E, E], [F, E, E, E, E, F, E, E, E, T, T, T, F, E, E]), ([F, E, E, E, E, E, F, E, T, E, T, E, F, T, E], [F, E, E, E, E, F, E, E, T, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_564 (And.intro z_23 trivial))

theorem z_566 : le (tf [F, E, E, E, E, E, T, F, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, E, T, T, F, E, E] [([F, E, E, E, E, E, E, F, T, E, T, T, F, E, E], [F, E, E, E, E, E, F, E, T, E, T, T, F, E, E]), ([F, E, E, E, E, E, T, F, E, E, T, E, F, T, E], [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_565 (And.intro z_178 trivial))

theorem z_567 : le (tf [F, E, E, E, E, E, T, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, T, E, T, F, E, E] [([F, E, E, E, E, E, E, T, F, T, E, T, F, E, E], [F, E, E, E, E, E, F, T, E, T, E, T, F, E, E]), ([F, E, E, E, E, E, T, E, F, E, T, T, F, E, E], [F, E, E, E, E, E, T, F, E, E, T, T, F, E, E]), ([F, E, E, E, E, E, T, E, F, T, E, E, F, T, E], [F, E, E, E, E, E, T, F, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 (And.intro z_566 (And.intro z_182 trivial)))

theorem z_568 : le (tf [E, F, E, E, E, E, T, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, F, T, T, E, F, E, E] [([E, F, E, E, E, E, E, T, F, T, T, E, F, E, E], [F, E, E, E, E, E, E, T, F, T, T, E, F, E, E]), ([E, F, E, E, E, E, T, E, F, T, E, T, F, E, E], [F, E, E, E, E, E, T, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_563 (And.intro z_567 trivial))

theorem z_569 : le (tf [E, F, E, E, E, E, T, T, F, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, E, E, T, F, E, E] [([E, F, E, E, E, E, T, E, F, T, E, T, F, E, E], [F, E, E, E, E, E, T, E, F, T, E, T, F, E, E]), ([E, F, E, E, E, E, T, T, F, E, E, E, F, T, E], [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_567 (And.intro z_195 trivial))

theorem z_570 : le (tf [E, E, F, E, E, E, T, T, F, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, F, E, T, E, F, E, E] [([E, E, F, E, E, E, T, E, F, T, T, E, F, E, E], [E, F, E, E, E, E, T, E, F, T, T, E, F, E, E]), ([E, E, F, E, E, E, T, T, F, E, E, T, F, E, E], [E, F, E, E, E, E, T, T, F, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_568 (And.intro z_569 trivial))

theorem z_571 : le (tf [F, E, E, E, E, T, F, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, T, E, F, E, T] [([F, E, E, E, E, E, F, T, E, E, T, E, F, E, T], [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T]), ([F, E, E, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 (And.intro z_202 trivial))

theorem z_572 : le (tf [F, E, E, E, E, T, E, F, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, E, F, T, E] [([F, E, E, E, E, E, T, F, E, E, T, E, F, T, E], [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E]), ([F, E, E, E, E, T, E, F, E, E, E, T, F, T, E], [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E]), ([F, E, E, E, E, T, E, F, E, E, T, E, F, E, T], [F, E, E, E, E, T, F, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 (And.intro z_203 (And.intro z_571 trivial)))

theorem z_573 : le (tf [F, E, E, E, E, T, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, E, T, T, F, E, E] [([F, E, E, E, E, E, T, E, F, E, T, T, F, E, E], [F, E, E, E, E, E, T, F, E, E, T, T, F, E, E]), ([F, E, E, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, E, E, T, E, F, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_566 (And.intro z_572 trivial))

theorem z_574 : le (tf [F, E, E, E, E, T, E, F, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, E, F, E, T] [([F, E, E, E, E, E, T, F, E, T, E, E, F, E, T], [F, E, E, E, E, F, T, E, E, T, E, E, F, E, T]), ([F, E, E, E, E, T, E, F, E, E, T, E, F, E, T], [F, E, E, E, E, T, F, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_181 (And.intro z_571 trivial))

theorem z_575 : le (tf [F, E, E, E, E, T, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, E, E, F, T, E] [([F, E, E, E, E, E, T, E, F, T, E, E, F, T, E], [F, E, E, E, E, E, T, F, E, T, E, E, F, T, E]), ([F, E, E, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, E, E, T, E, F, E, E, T, E, F, T, E]), ([F, E, E, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, E, E, T, E, F, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_182 (And.intro z_572 (And.intro z_574 trivial)))

theorem z_576 : le (tf [E, F, E, E, E, T, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, F, T, E, T, F, E, E] [([E, F, E, E, E, E, T, E, F, T, E, T, F, E, E], [F, E, E, E, E, E, T, E, F, T, E, T, F, E, E]), ([E, F, E, E, E, T, E, E, F, E, T, T, F, E, E], [F, E, E, E, E, T, E, E, F, E, T, T, F, E, E]), ([E, F, E, E, E, T, E, E, F, T, E, E, F, T, E], [F, E, E, E, E, T, E, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_567 (And.intro z_573 (And.intro z_575 trivial)))

theorem z_577 : le (tf [E, E, F, E, E, T, E, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, F, T, T, E, F, E, E] [([E, E, F, E, E, E, T, E, F, T, T, E, F, E, E], [E, F, E, E, E, E, T, E, F, T, T, E, F, E, E]), ([E, E, F, E, E, T, E, E, F, T, E, T, F, E, E], [E, F, E, E, E, T, E, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_568 (And.intro z_576 trivial))

theorem z_578 : le (tf [F, E, E, E, E, T, E, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, E, E, F, E, T] [([F, E, E, E, E, E, T, T, F, E, E, E, F, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T]), ([F, E, E, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, E, E, T, E, F, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 (And.intro z_574 trivial))

theorem z_579 : le (tf [E, F, E, E, E, T, E, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, F, E, E, E, F, T, E] [([E, F, E, E, E, E, T, T, F, E, E, E, F, T, E], [F, E, E, E, E, E, T, T, F, E, E, E, F, T, E]), ([E, F, E, E, E, T, E, E, F, T, E, E, F, T, E], [F, E, E, E, E, T, E, E, F, T, E, E, F, T, E]), ([E, F, E, E, E, T, E, T, F, E, E, E, F, E, T], [F, E, E, E, E, T, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_195 (And.intro z_575 (And.intro z_578 trivial)))

theorem z_580 : le (tf [E, E, F, E, E, T, E, T, F, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, E, E, T, F, E, E] [([E, E, F, E, E, E, T, T, F, E, E, T, F, E, E], [E, F, E, E, E, E, T, T, F, E, E, T, F, E, E]), ([E, E, F, E, E, T, E, E, F, T, E, T, F, E, E], [E, F, E, E, E, T, E, E, F, T, E, T, F, E, E]), ([E, E, F, E, E, T, E, T, F, E, E, E, F, T, E], [E, F, E, E, E, T, E, T, F, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_569 (And.intro z_576 (And.intro z_579 trivial)))

theorem z_581 : le (tf [E, E, E, F, E, T, E, T, F, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, F, E, T, E, F, E, E] [([E, E, E, F, E, E, T, T, F, E, T, E, F, E, E], [E, E, F, E, E, E, T, T, F, E, T, E, F, E, E]), ([E, E, E, F, E, T, E, E, F, T, T, E, F, E, E], [E, E, F, E, E, T, E, E, F, T, T, E, F, E, E]), ([E, E, E, F, E, T, E, T, F, E, E, T, F, E, E], [E, E, F, E, E, T, E, T, F, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_570 (And.intro z_577 (And.intro z_580 trivial)))

theorem z_582 : le (tf [F, E, E, E, F, T, E, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, T, E, E, F, E, T] [([F, E, E, E, F, E, T, E, E, T, E, E, F, E, T], [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T]), ([F, E, E, E, F, T, E, E, E, E, T, E, F, E, T], [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 (And.intro z_218 trivial))

theorem z_583 : le (tf [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E] [([F, E, E, E, E, E, F, T, E, T, E, E, F, T, E], [F, E, E, E, E, F, E, T, E, T, E, E, F, T, E]), ([F, E, E, E, E, T, F, E, E, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E]), ([F, E, E, E, E, T, F, E, E, T, E, E, F, E, T], [F, E, E, E, F, T, E, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_561 (And.intro z_219 (And.intro z_582 trivial)))

theorem z_584 : le (tf [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E] [([F, E, E, E, E, E, T, F, E, T, E, T, F, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]), ([F, E, E, E, E, T, E, F, E, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, E, F, T, E], [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_355 (And.intro z_583 trivial)))

theorem z_585 : le (tf [F, E, E, E, E, T, E, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, T, E, F, E, E] [([F, E, E, E, E, E, T, E, F, T, T, E, F, E, E], [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]), ([F, E, E, E, E, T, E, E, F, T, E, T, F, E, E], [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_584 trivial))

theorem z_586 : le (tf [F, E, E, E, T, E, E, F, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, T, T, F, E, E] [([F, E, E, E, E, T, E, F, E, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([F, E, E, E, T, E, E, F, E, E, T, E, F, T, E], [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_490 trivial))

theorem z_587 : le (tf [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T] [([F, E, E, E, E, T, F, E, E, T, E, E, F, E, T], [F, E, E, E, F, T, E, E, E, T, E, E, F, E, T]), ([F, E, E, E, T, E, F, E, E, E, T, E, F, E, T], [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_582 (And.intro z_489 trivial))

theorem z_588 : le (tf [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E] [([F, E, E, E, E, T, E, F, E, T, E, E, F, T, E], [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E]), ([F, E, E, E, T, E, E, F, E, E, T, E, F, T, E], [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E]), ([F, E, E, E, T, E, E, F, E, T, E, E, F, E, T], [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_490 (And.intro z_587 trivial)))

theorem z_589 : le (tf [F, E, E, E, T, E, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, E, T, F, E, E] [([F, E, E, E, E, T, E, E, F, T, E, T, F, E, E], [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E]), ([F, E, E, E, T, E, E, E, F, E, T, T, F, E, E], [F, E, E, E, T, E, E, F, E, E, T, T, F, E, E]), ([F, E, E, E, T, E, E, E, F, T, E, E, F, T, E], [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 (And.intro z_586 (And.intro z_588 trivial)))

theorem z_590 : le (tf [E, F, E, E, T, E, E, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, T, T, E, F, E, E] [([E, F, E, E, E, T, E, E, F, T, T, E, F, E, E], [F, E, E, E, E, T, E, E, F, T, T, E, F, E, E]), ([E, F, E, E, T, E, E, E, F, T, E, T, F, E, E], [F, E, E, E, T, E, E, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_585 (And.intro z_589 trivial))

theorem z_591 : le (tf [F, E, E, T, E, E, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, T, T, F, E, E] [([F, E, E, E, T, E, E, E, F, E, T, T, F, E, E], [F, E, E, E, T, E, E, F, E, E, T, T, F, E, E]), ([F, E, E, T, E, E, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_586 (And.intro z_505 trivial))

theorem z_592 : le (tf [F, E, E, T, E, E, E, F, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, E, F, E, T] [([F, E, E, E, T, E, E, F, E, T, E, E, F, E, T], [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T]), ([F, E, E, T, E, E, E, F, E, E, T, E, F, E, T], [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_587 (And.intro z_504 trivial))

theorem z_593 : le (tf [F, E, E, T, E, E, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, E, E, F, T, E] [([F, E, E, E, T, E, E, E, F, T, E, E, F, T, E], [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E]), ([F, E, E, T, E, E, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E]), ([F, E, E, T, E, E, E, E, F, T, E, E, F, E, T], [F, E, E, T, E, E, E, F, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_588 (And.intro z_505 (And.intro z_592 trivial)))

theorem z_594 : le (tf [E, F, E, T, E, E, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, T, E, T, F, E, E] [([E, F, E, E, T, E, E, E, F, T, E, T, F, E, E], [F, E, E, E, T, E, E, E, F, T, E, T, F, E, E]), ([E, F, E, T, E, E, E, E, F, E, T, T, F, E, E], [F, E, E, T, E, E, E, E, F, E, T, T, F, E, E]), ([E, F, E, T, E, E, E, E, F, T, E, E, F, T, E], [F, E, E, T, E, E, E, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_589 (And.intro z_591 (And.intro z_593 trivial)))

theorem z_595 : le (tf [E, E, F, T, E, E, E, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, E, F, T, T, E, F, E, E] [([E, E, F, E, T, E, E, E, F, T, T, E, F, E, E], [E, F, E, E, T, E, E, E, F, T, T, E, F, E, E]), ([E, E, F, T, E, E, E, E, F, T, E, T, F, E, E], [E, F, E, T, E, E, E, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_590 (And.intro z_594 trivial))

theorem z_596 : le (tf [F, E, E, E, E, F, E, T, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, F, T, T, E, E] [([F, E, E, E, E, F, E, E, T, E, F, T, T, E, E], [F, E, E, E, F, E, E, E, T, E, F, T, T, E, E]), ([F, E, E, E, E, F, E, T, E, E, F, T, E, T, E], [F, E, E, E, F, E, E, T, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_321 (And.intro z_303 trivial))

theorem z_597 : le (tf [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E] [([F, E, E, E, E, E, F, E, T, T, F, E, T, E, E], [F, E, E, E, E, F, E, E, T, T, F, E, T, E, E]), ([F, E, E, E, E, E, F, T, E, E, F, T, T, E, E], [F, E, E, E, E, F, E, T, E, E, F, T, T, E, E]), ([F, E, E, E, E, E, F, T, E, T, F, E, E, T, E], [F, E, E, E, E, F, E, T, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_323 (And.intro z_596 (And.intro z_400 trivial)))

theorem z_598 : le (tf [F, E, E, E, E, E, E, T, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, F, T, F, T, E, E, E] [([F, E, E, E, E, E, E, T, F, T, F, E, T, E, E], [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_597 trivial)

theorem z_599 : le (tf [F, E, E, E, E, F, E, E, E, T, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, F, T, T, E, E] [([F, E, E, E, E, F, E, E, E, T, F, T, E, T, E], [F, E, E, E, F, E, E, E, E, T, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_289 trivial)

theorem z_600 : le (tf [F, E, E, E, E, E, F, E, T, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, E, F, T, T, E, E] [([F, E, E, E, E, E, F, E, E, T, F, T, T, E, E], [F, E, E, E, E, F, E, E, E, T, F, T, T, E, E]), ([F, E, E, E, E, E, F, E, T, E, F, T, E, T, E], [F, E, E, E, E, F, E, E, T, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_599 (And.intro z_294 trivial))

theorem z_601 : le (tf [F, E, E, E, E, E, T, F, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, E, F, T, T, E, E] [([F, E, E, E, E, E, E, F, T, E, F, T, T, E, E], [F, E, E, E, E, E, F, E, T, E, F, T, T, E, E]), ([F, E, E, E, E, E, T, F, E, E, F, T, E, T, E], [F, E, E, E, E, F, T, E, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_600 (And.intro z_308 trivial))

theorem z_602 : le (tf [F, E, E, E, E, E, T, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, T, F, E, T, E, E] [([F, E, E, E, E, E, E, T, F, T, F, E, T, E, E], [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E]), ([F, E, E, E, E, E, T, E, F, E, F, T, T, E, E], [F, E, E, E, E, E, T, F, E, E, F, T, T, E, E]), ([F, E, E, E, E, E, T, E, F, T, F, E, E, T, E], [F, E, E, E, E, E, T, F, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_597 (And.intro z_601 (And.intro z_312 trivial)))

theorem z_603 : le (tf [E, F, E, E, E, E, T, E, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, F, T, F, T, E, E, E] [([E, F, E, E, E, E, E, T, F, T, F, T, E, E, E], [F, E, E, E, E, E, E, T, F, T, F, T, E, E, E]), ([E, F, E, E, E, E, T, E, F, T, F, E, T, E, E], [F, E, E, E, E, E, T, E, F, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_598 (And.intro z_602 trivial))

theorem z_604 : le (tf [E, F, E, E, E, E, T, T, F, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, E, F, E, T, E, E] [([E, F, E, E, E, E, T, E, F, T, F, E, T, E, E], [F, E, E, E, E, E, T, E, F, T, F, E, T, E, E]), ([E, F, E, E, E, E, T, T, F, E, F, E, E, T, E], [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_602 (And.intro z_314 trivial))

theorem z_605 : le (tf [E, E, F, E, E, E, T, T, F, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, F, E, F, T, E, E, E] [([E, E, F, E, E, E, T, E, F, T, F, T, E, E, E], [E, F, E, E, E, E, T, E, F, T, F, T, E, E, E]), ([E, E, F, E, E, E, T, T, F, E, F, E, T, E, E], [E, F, E, E, E, E, T, T, F, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 (And.intro z_604 trivial))

theorem z_606 : le (tf [F, E, E, F, E, E, E, T, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, E, F, E, E, T, T] [([F, E, E, F, E, E, E, E, T, E, F, E, E, T, T], [F, E, F, E, E, E, E, E, T, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_290 trivial)

theorem z_607 : le (tf [F, E, E, E, F, E, E, T, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, E, F, E, T, E, T] [([F, E, E, E, F, E, E, E, T, E, F, E, T, E, T], [F, E, E, F, E, E, E, E, T, E, F, E, T, E, T]), ([F, E, E, E, F, E, E, T, E, E, F, E, E, T, T], [F, E, E, F, E, E, E, T, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_291 (And.intro z_606 trivial))

theorem z_608 : le (tf [F, E, E, E, E, F, E, T, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, F, E, T, T, E] [([F, E, E, E, E, F, E, E, T, E, F, E, T, T, E], [F, E, E, E, F, E, E, E, T, E, F, E, T, T, E]), ([F, E, E, E, E, F, E, T, E, E, F, E, T, E, T], [F, E, E, E, F, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_292 (And.intro z_607 trivial))

theorem z_609 : le (tf [F, E, E, F, E, T, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, E, F, E, E, T, T] [([F, E, E, F, E, E, T, E, E, E, F, E, E, T, T], [F, E, F, E, E, E, T, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 trivial)

theorem z_610 : le (tf [F, E, E, E, F, T, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, F, E, T, E, T] [([F, E, E, E, F, E, T, E, E, E, F, E, T, E, T], [F, E, E, F, E, E, T, E, E, E, F, E, T, E, T]), ([F, E, E, E, F, T, E, E, E, E, F, E, E, T, T], [F, E, E, F, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_305 (And.intro z_609 trivial))

theorem z_611 : le (tf [F, E, E, E, E, T, F, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, F, E, T, T, E] [([F, E, E, E, E, E, F, T, E, E, F, E, T, T, E], [F, E, E, E, E, F, E, T, E, E, F, E, T, T, E]), ([F, E, E, E, E, T, F, E, E, E, F, E, T, E, T], [F, E, E, E, F, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_608 (And.intro z_610 trivial))

theorem z_612 : le (tf [F, E, E, E, E, F, E, T, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, F, T, E, E, T] [([F, E, E, E, E, F, E, E, T, E, F, T, E, E, T], [F, E, E, E, F, E, E, E, T, E, F, T, E, E, T]), ([F, E, E, E, E, F, E, T, E, E, F, E, T, E, T], [F, E, E, E, F, E, E, T, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_293 (And.intro z_607 trivial))

theorem z_613 : le (tf [F, E, E, E, E, T, F, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, F, T, E, E, T] [([F, E, E, E, E, E, F, T, E, E, F, T, E, E, T], [F, E, E, E, E, F, E, T, E, E, F, T, E, E, T]), ([F, E, E, E, E, T, F, E, E, E, F, E, T, E, T], [F, E, E, E, F, T, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_612 (And.intro z_610 trivial))

theorem z_614 : le (tf [F, E, E, E, E, T, E, F, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, F, T, E, T, E] [([F, E, E, E, E, E, T, F, E, E, F, T, E, T, E], [F, E, E, E, E, F, T, E, E, E, F, T, E, T, E]), ([F, E, E, E, E, T, E, F, E, E, F, E, T, T, E], [F, E, E, E, E, T, F, E, E, E, F, E, T, T, E]), ([F, E, E, E, E, T, E, F, E, E, F, T, E, E, T], [F, E, E, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_308 (And.intro z_611 (And.intro z_613 trivial)))

theorem z_615 : le (tf [F, E, E, E, E, T, E, E, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, E, F, T, T, E, E] [([F, E, E, E, E, E, T, E, F, E, F, T, T, E, E], [F, E, E, E, E, E, T, F, E, E, F, T, T, E, E]), ([F, E, E, E, E, T, E, E, F, E, F, T, E, T, E], [F, E, E, E, E, T, E, F, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_601 (And.intro z_614 trivial))

theorem z_616 : le (tf [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T] [([F, E, E, E, E, E, T, F, E, T, F, E, E, E, T], [F, E, E, E, E, F, T, E, E, T, F, E, E, E, T]), ([F, E, E, E, E, T, E, F, E, E, F, T, E, E, T], [F, E, E, E, E, T, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_311 (And.intro z_613 trivial))

theorem z_617 : le (tf [F, E, E, E, E, T, E, E, F, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, F, E, E, T, E] [([F, E, E, E, E, E, T, E, F, T, F, E, E, T, E], [F, E, E, E, E, E, T, F, E, T, F, E, E, T, E]), ([F, E, E, E, E, T, E, E, F, E, F, T, E, T, E], [F, E, E, E, E, T, E, F, E, E, F, T, E, T, E]), ([F, E, E, E, E, T, E, E, F, T, F, E, E, E, T], [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_614 (And.intro z_616 trivial)))

theorem z_618 : le (tf [E, F, E, E, E, T, E, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, F, T, F, E, T, E, E] [([E, F, E, E, E, E, T, E, F, T, F, E, T, E, E], [F, E, E, E, E, E, T, E, F, T, F, E, T, E, E]), ([E, F, E, E, E, T, E, E, F, E, F, T, T, E, E], [F, E, E, E, E, T, E, E, F, E, F, T, T, E, E]), ([E, F, E, E, E, T, E, E, F, T, F, E, E, T, E], [F, E, E, E, E, T, E, E, F, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_602 (And.intro z_615 (And.intro z_617 trivial)))

theorem z_619 : le (tf [E, E, F, E, E, T, E, E, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, F, T, F, T, E, E, E] [([E, E, F, E, E, E, T, E, F, T, F, T, E, E, E], [E, F, E, E, E, E, T, E, F, T, F, T, E, E, E]), ([E, E, F, E, E, T, E, E, F, T, F, E, T, E, E], [E, F, E, E, E, T, E, E, F, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_603 (And.intro z_618 trivial))

theorem z_620 : le (tf [F, E, E, E, E, T, E, T, F, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, F, E, E, E, T] [([F, E, E, E, E, E, T, T, F, E, F, E, E, E, T], [F, E, E, E, E, E, T, T, F, F, E, E, E, E, T]), ([F, E, E, E, E, T, E, E, F, T, F, E, E, E, T], [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_616 trivial))

theorem z_621 : le (tf [E, F, E, E, E, T, E, T, F, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, F, E, F, E, E, T, E] [([E, F, E, E, E, E, T, T, F, E, F, E, E, T, E], [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E]), ([E, F, E, E, E, T, E, E, F, T, F, E, E, T, E], [F, E, E, E, E, T, E, E, F, T, F, E, E, T, E]), ([E, F, E, E, E, T, E, T, F, E, F, E, E, E, T], [F, E, E, E, E, T, E, T, F, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_314 (And.intro z_617 (And.intro z_620 trivial)))

theorem z_622 : le (tf [E, E, F, E, E, T, E, T, F, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, E, F, E, T, E, E] [([E, E, F, E, E, E, T, T, F, E, F, E, T, E, E], [E, F, E, E, E, E, T, T, F, E, F, E, T, E, E]), ([E, E, F, E, E, T, E, E, F, T, F, E, T, E, E], [E, F, E, E, E, T, E, E, F, T, F, E, T, E, E]), ([E, E, F, E, E, T, E, T, F, E, F, E, E, T, E], [E, F, E, E, E, T, E, T, F, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_604 (And.intro z_618 (And.intro z_621 trivial)))

theorem z_623 : le (tf [E, E, E, F, E, T, E, T, F, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, F, E, F, T, E, E, E] [([E, E, E, F, E, E, T, T, F, E, F, T, E, E, E], [E, E, F, E, E, E, T, T, F, E, F, T, E, E, E]), ([E, E, E, F, E, T, E, E, F, T, F, T, E, E, E], [E, E, F, E, E, T, E, E, F, T, F, T, E, E, E]), ([E, E, E, F, E, T, E, T, F, E, F, E, T, E, E], [E, E, F, E, E, T, E, T, F, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_605 (And.intro z_619 (And.intro z_622 trivial)))

theorem z_624 : le (tf [F, E, E, E, E, T, F, E, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, F, T, T, E, E] [([F, E, E, E, E, E, F, T, E, E, F, T, T, E, E], [F, E, E, E, E, F, E, T, E, E, F, T, T, E, E]), ([F, E, E, E, E, T, F, E, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_596 (And.intro z_405 trivial))

theorem z_625 : le (tf [F, E, E, E, E, T, E, F, E, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, F, E, T, E, E] [([F, E, E, E, E, E, T, F, E, T, F, E, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E]), ([F, E, E, E, E, T, E, F, E, E, F, T, T, E, E], [F, E, E, E, E, T, F, E, E, E, F, T, T, E, E]), ([F, E, E, E, E, T, E, F, E, T, F, E, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 (And.intro z_624 (And.intro z_407 trivial)))

theorem z_626 : le (tf [F, E, E, E, E, T, E, E, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, F, T, E, E, E] [([F, E, E, E, E, E, T, E, F, T, F, T, E, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]), ([F, E, E, E, E, T, E, E, F, T, F, E, T, E, E], [F, E, E, E, E, T, E, F, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_625 trivial))

theorem z_627 : le (tf [F, E, F, E, T, E, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, E, E, F, E, E, T, T] [([F, E, F, E, E, T, E, E, E, E, F, E, E, T, T], [F, F, E, E, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_628 : le (tf [F, E, E, F, T, E, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, E, F, E, T, E, T] [([F, E, E, F, E, T, E, E, E, E, F, E, T, E, T], [F, E, F, E, E, T, E, E, E, E, F, E, T, E, T]), ([F, E, E, F, T, E, E, E, E, E, F, E, E, T, T], [F, E, F, E, T, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_627 trivial))

theorem z_629 : le (tf [F, E, E, E, T, F, E, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, F, E, T, T, E] [([F, E, E, E, E, F, T, E, E, E, F, E, T, T, E], [F, E, E, E, F, E, T, E, E, E, F, E, T, T, E]), ([F, E, E, E, T, F, E, E, E, E, F, E, T, E, T], [F, E, E, F, T, E, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_306 (And.intro z_628 trivial))

theorem z_630 : le (tf [F, E, E, E, T, F, E, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, F, T, E, E, T] [([F, E, E, E, E, F, T, E, E, E, F, T, E, E, T], [F, E, E, E, F, E, T, E, E, E, F, T, E, E, T]), ([F, E, E, E, T, F, E, E, E, E, F, E, T, E, T], [F, E, E, F, T, E, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_307 (And.intro z_628 trivial))

theorem z_631 : le (tf [F, E, E, E, T, E, F, E, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, F, T, E, T, E] [([F, E, E, E, E, T, F, E, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E]), ([F, E, E, E, T, E, F, E, E, E, F, E, T, T, E], [F, E, E, E, T, F, E, E, E, E, F, E, T, T, E]), ([F, E, E, E, T, E, F, E, E, E, F, T, E, E, T], [F, E, E, E, T, F, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_405 (And.intro z_629 (And.intro z_630 trivial)))

theorem z_632 : le (tf [F, E, E, E, T, E, E, F, E, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, F, T, T, E, E] [([F, E, E, E, E, T, E, F, E, E, F, T, T, E, E], [F, E, E, E, E, T, F, E, E, E, F, T, T, E, E]), ([F, E, E, E, T, E, E, F, E, E, F, T, E, T, E], [F, E, E, E, T, E, F, E, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_624 (And.intro z_631 trivial))

theorem z_633 : le (tf [F, E, E, E, T, E, F, E, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, F, E, E, E, T] [([F, E, E, E, E, T, F, E, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T]), ([F, E, E, E, T, E, F, E, E, E, F, T, E, E, T], [F, E, E, E, T, F, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_406 (And.intro z_630 trivial))

theorem z_634 : le (tf [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E] [([F, E, E, E, E, T, E, F, E, T, F, E, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E]), ([F, E, E, E, T, E, E, F, E, E, F, T, E, T, E], [F, E, E, E, T, E, F, E, E, E, F, T, E, T, E]), ([F, E, E, E, T, E, E, F, E, T, F, E, E, E, T], [F, E, E, E, T, E, F, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_407 (And.intro z_631 (And.intro z_633 trivial)))

theorem z_635 : le (tf [F, E, E, E, T, E, E, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, F, E, T, E, E] [([F, E, E, E, E, T, E, E, F, T, F, E, T, E, E], [F, E, E, E, E, T, E, F, E, T, F, E, T, E, E]), ([F, E, E, E, T, E, E, E, F, E, F, T, T, E, E], [F, E, E, E, T, E, E, F, E, E, F, T, T, E, E]), ([F, E, E, E, T, E, E, E, F, T, F, E, E, T, E], [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_625 (And.intro z_632 (And.intro z_634 trivial)))

theorem z_636 : le (tf [E, F, E, E, T, E, E, E, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, T, F, T, E, E, E] [([E, F, E, E, E, T, E, E, F, T, F, T, E, E, E], [F, E, E, E, E, T, E, E, F, T, F, T, E, E, E]), ([E, F, E, E, T, E, E, E, F, T, F, E, T, E, E], [F, E, E, E, T, E, E, E, F, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_626 (And.intro z_635 trivial))

theorem z_637 : le (tf [F, E, E, T, F, E, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, F, E, E, T, T] [([F, E, E, E, F, T, E, E, E, E, F, E, E, T, T], [F, E, E, F, E, T, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_609 trivial)

theorem z_638 : le (tf [F, E, E, T, E, F, E, E, E, E, F, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, E, F, E, T, E, T] [([F, E, E, E, T, F, E, E, E, E, F, E, T, E, T], [F, E, E, F, T, E, E, E, E, E, F, E, T, E, T]), ([F, E, E, T, E, F, E, E, E, E, F, E, E, T, T], [F, E, E, T, F, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_628 (And.intro z_637 trivial))

theorem z_639 : le (tf [F, E, E, T, E, E, F, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, F, E, T, T, E] [([F, E, E, E, T, E, F, E, E, E, F, E, T, T, E], [F, E, E, E, T, F, E, E, E, E, F, E, T, T, E]), ([F, E, E, T, E, E, F, E, E, E, F, E, T, E, T], [F, E, E, T, E, F, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_629 (And.intro z_638 trivial))

theorem z_640 : le (tf [F, E, E, T, E, E, F, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, F, T, E, E, T] [([F, E, E, E, T, E, F, E, E, E, F, T, E, E, T], [F, E, E, E, T, F, E, E, E, E, F, T, E, E, T]), ([F, E, E, T, E, E, F, E, E, E, F, E, T, E, T], [F, E, E, T, E, F, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_630 (And.intro z_638 trivial))

theorem z_641 : le (tf [F, E, E, T, E, E, E, F, E, E, F, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, F, T, E, T, E] [([F, E, E, E, T, E, E, F, E, E, F, T, E, T, E], [F, E, E, E, T, E, F, E, E, E, F, T, E, T, E]), ([F, E, E, T, E, E, E, F, E, E, F, E, T, T, E], [F, E, E, T, E, E, F, E, E, E, F, E, T, T, E]), ([F, E, E, T, E, E, E, F, E, E, F, T, E, E, T], [F, E, E, T, E, E, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_631 (And.intro z_639 (And.intro z_640 trivial)))

theorem z_642 : le (tf [F, E, E, T, E, E, E, E, F, E, F, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, F, T, T, E, E] [([F, E, E, E, T, E, E, E, F, E, F, T, T, E, E], [F, E, E, E, T, E, E, F, E, E, F, T, T, E, E]), ([F, E, E, T, E, E, E, E, F, E, F, T, E, T, E], [F, E, E, T, E, E, E, F, E, E, F, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_632 (And.intro z_641 trivial))

theorem z_643 : le (tf [F, E, E, T, E, E, E, F, E, T, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, F, E, E, E, T] [([F, E, E, E, T, E, E, F, E, T, F, E, E, E, T], [F, E, E, E, T, E, F, E, E, T, F, E, E, E, T]), ([F, E, E, T, E, E, E, F, E, E, F, T, E, E, T], [F, E, E, T, E, E, F, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_633 (And.intro z_640 trivial))

theorem z_644 : le (tf [F, E, E, T, E, E, E, E, F, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, F, E, E, T, E] [([F, E, E, E, T, E, E, E, F, T, F, E, E, T, E], [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E]), ([F, E, E, T, E, E, E, E, F, E, F, T, E, T, E], [F, E, E, T, E, E, E, F, E, E, F, T, E, T, E]), ([F, E, E, T, E, E, E, E, F, T, F, E, E, E, T], [F, E, E, T, E, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_634 (And.intro z_641 (And.intro z_643 trivial)))

theorem z_645 : le (tf [E, F, E, T, E, E, E, E, F, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, T, F, E, T, E, E] [([E, F, E, E, T, E, E, E, F, T, F, E, T, E, E], [F, E, E, E, T, E, E, E, F, T, F, E, T, E, E]), ([E, F, E, T, E, E, E, E, F, E, F, T, T, E, E], [F, E, E, T, E, E, E, E, F, E, F, T, T, E, E]), ([E, F, E, T, E, E, E, E, F, T, F, E, E, T, E], [F, E, E, T, E, E, E, E, F, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_635 (And.intro z_642 (And.intro z_644 trivial)))

theorem z_646 : le (tf [E, E, F, T, E, E, E, E, F, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, E, F, T, F, T, E, E, E] [([E, E, F, E, T, E, E, E, F, T, F, T, E, E, E], [E, F, E, E, T, E, E, E, F, T, F, T, E, E, E]), ([E, E, F, T, E, E, E, E, F, T, F, E, T, E, E], [E, F, E, T, E, E, E, E, F, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_636 (And.intro z_645 trivial))

theorem z_647 : le (tf [F, E, E, E, E, F, E, T, T, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, F, E, E, E, T] [([F, E, E, E, E, F, E, T, E, T, F, E, E, E, T], [F, E, E, E, F, E, E, T, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_310 trivial)

theorem z_648 : le (tf [F, E, E, E, E, E, F, T, T, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, T, E, F, E, E, T, E] [([F, E, E, E, E, E, F, T, E, T, F, E, E, T, E], [F, E, E, E, E, F, E, T, E, T, F, E, E, T, E]), ([F, E, E, E, E, E, F, T, T, E, F, E, E, E, T], [F, E, E, E, E, F, E, T, T, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_400 (And.intro z_647 trivial))

theorem z_649 : le (tf [E, F, E, E, E, E, F, T, T, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, F, T, T, E, F, E, T, E, E] [([E, F, E, E, E, E, F, T, E, T, F, E, T, E, E], [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E]), ([E, F, E, E, E, E, F, T, T, E, F, E, E, T, E], [F, E, E, E, E, E, F, T, T, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_597 (And.intro z_648 trivial))

theorem z_650 : le (tf [E, F, E, E, E, T, F, E, E, T, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, T, F, E, T, E, E] [([E, F, E, E, E, E, F, T, E, T, F, E, T, E, E], [F, E, E, E, E, E, F, T, E, T, F, E, T, E, E]), ([E, F, E, E, E, T, F, E, E, E, F, T, T, E, E], [F, E, E, E, E, T, F, E, E, E, F, T, T, E, E]), ([E, F, E, E, E, T, F, E, E, T, F, E, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_597 (And.intro z_624 (And.intro z_407 trivial)))

theorem z_651 : le (tf [F, E, E, E, E, T, F, E, T, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, F, E, E, E, T] [([F, E, E, E, E, E, F, T, T, E, F, E, E, E, T], [F, E, E, E, E, F, E, T, T, E, F, E, E, E, T]), ([F, E, E, E, E, T, F, E, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_647 (And.intro z_406 trivial))

theorem z_652 : le (tf [E, F, E, E, E, T, F, E, T, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, T, E, F, E, E, T, E] [([E, F, E, E, E, E, F, T, T, E, F, E, E, T, E], [F, E, E, E, E, E, F, T, T, E, F, E, E, T, E]), ([E, F, E, E, E, T, F, E, E, T, F, E, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E]), ([E, F, E, E, E, T, F, E, T, E, F, E, E, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_648 (And.intro z_407 (And.intro z_651 trivial)))

theorem z_653 : le (tf [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E] [([E, E, F, E, E, E, F, T, T, E, F, E, T, E, E], [E, F, E, E, E, E, F, T, T, E, F, E, T, E, E]), ([E, E, F, E, E, T, F, E, E, T, F, E, T, E, E], [E, F, E, E, E, T, F, E, E, T, F, E, T, E, E]), ([E, E, F, E, E, T, F, E, T, E, F, E, E, T, E], [E, F, E, E, E, T, F, E, T, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_649 (And.intro z_650 (And.intro z_652 trivial)))

theorem z_654 : le (tf [E, F, E, E, E, T, F, T, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, E, F, E, E, E, T] [([E, F, E, E, E, T, F, E, T, E, F, E, E, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_651 trivial)

theorem z_655 : le (tf [E, E, F, E, E, T, F, T, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, F, T, E, E, F, E, E, T, E] [([E, E, F, E, E, T, F, E, T, E, F, E, E, T, E], [E, F, E, E, E, T, F, E, T, E, F, E, E, T, E]), ([E, E, F, E, E, T, F, T, E, E, F, E, E, E, T], [E, F, E, E, E, T, F, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_652 (And.intro z_654 trivial))

theorem z_656 : le (tf [E, E, E, F, E, T, F, T, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, F, T, E, E, F, E, T, E, E] [([E, E, E, F, E, T, F, E, T, E, F, E, T, E, E], [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E]), ([E, E, E, F, E, T, F, T, E, E, F, E, E, T, E], [E, E, F, E, E, T, F, T, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_653 (And.intro z_655 trivial))

theorem z_657 : le (tf [F, E, F, E, E, E, E, E, E, F, T, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, F, T, E, T, T, E] [([F, E, F, E, E, E, E, E, E, F, E, T, T, T, E], [F, F, E, E, E, E, E, E, E, F, E, T, T, T, E]), ([F, E, F, E, E, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 (And.intro z_73 trivial))

theorem z_658 : le (tf [F, E, F, E, E, E, E, E, E, F, T, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, F, T, T, E, E, T] [([F, E, F, E, E, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 trivial)

theorem z_659 : le (tf [F, E, E, F, E, E, E, E, E, F, T, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, F, T, T, E, T, E] [([F, E, E, F, E, E, E, E, E, F, T, E, T, T, E], [F, E, F, E, E, E, E, E, E, F, T, E, T, T, E]), ([F, E, E, F, E, E, E, E, E, F, T, T, E, E, T], [F, E, F, E, E, E, E, E, E, F, T, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_657 (And.intro z_658 trivial))

theorem z_660 : le (tf [F, E, E, E, F, E, E, E, E, F, T, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, F, T, T, T, E, E] [([F, E, E, E, F, E, E, E, E, F, T, T, E, T, E], [F, E, E, F, E, E, E, E, E, F, T, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_659 trivial)

theorem z_661 : le (tf [F, E, F, E, E, E, E, E, T, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, T, F, E, E, T, E, T] [([F, E, F, E, E, E, E, E, E, F, T, E, T, E, T], [F, F, E, E, E, E, E, E, E, F, T, E, T, E, T]), ([F, E, F, E, E, E, E, E, T, F, E, E, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 (And.intro z_119 trivial))

theorem z_662 : le (tf [F, E, E, F, E, E, E, E, T, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, F, E, E, T, T, E] [([F, E, E, F, E, E, E, E, E, F, T, E, T, T, E], [F, E, F, E, E, E, E, E, E, F, T, E, T, T, E]), ([F, E, E, F, E, E, E, E, T, F, E, E, T, E, T], [F, E, F, E, E, E, E, E, T, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_657 (And.intro z_661 trivial))

theorem z_663 : le (tf [F, E, E, F, E, E, E, E, T, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, F, E, T, E, E, T] [([F, E, E, F, E, E, E, E, E, F, T, T, E, E, T], [F, E, F, E, E, E, E, E, E, F, T, T, E, E, T]), ([F, E, E, F, E, E, E, E, T, F, E, E, T, E, T], [F, E, F, E, E, E, E, E, T, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_658 (And.intro z_661 trivial))

theorem z_664 : le (tf [F, E, E, E, F, E, E, E, T, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, F, E, T, E, T, E] [([F, E, E, E, F, E, E, E, E, F, T, T, E, T, E], [F, E, E, F, E, E, E, E, E, F, T, T, E, T, E]), ([F, E, E, E, F, E, E, E, T, F, E, E, T, T, E], [F, E, E, F, E, E, E, E, T, F, E, E, T, T, E]), ([F, E, E, E, F, E, E, E, T, F, E, T, E, E, T], [F, E, E, F, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_659 (And.intro z_662 (And.intro z_663 trivial)))

theorem z_665 : le (tf [F, E, E, E, E, F, E, E, T, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, F, E, T, T, E, E] [([F, E, E, E, E, F, E, E, E, F, T, T, T, E, E], [F, E, E, E, F, E, E, E, E, F, T, T, T, E, E]), ([F, E, E, E, E, F, E, E, T, F, E, T, E, T, E], [F, E, E, E, F, E, E, E, T, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_660 (And.intro z_664 trivial))

theorem z_666 : le (tf [F, E, E, E, F, E, E, E, T, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, T, F, T, E, E, E, T] [([F, E, E, E, F, E, E, E, T, F, E, T, E, E, T], [F, E, E, F, E, E, E, E, T, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_663 trivial)

theorem z_667 : le (tf [F, E, E, E, E, F, E, E, T, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, F, T, E, E, T, E] [([F, E, E, E, E, F, E, E, T, F, E, T, E, T, E], [F, E, E, E, F, E, E, E, T, F, E, T, E, T, E]), ([F, E, E, E, E, F, E, E, T, F, T, E, E, E, T], [F, E, E, E, F, E, E, E, T, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_664 (And.intro z_666 trivial))

theorem z_668 : le (tf [F, E, E, E, E, E, F, E, T, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, F, T, E, T, E, E] [([F, E, E, E, E, E, F, E, T, F, E, T, T, E, E], [F, E, E, E, E, F, E, E, T, F, E, T, T, E, E]), ([F, E, E, E, E, E, F, E, T, F, T, E, E, T, E], [F, E, E, E, E, F, E, E, T, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_665 (And.intro z_667 trivial))

theorem z_669 : le (tf [F, E, F, E, E, E, E, T, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, T, E, F, E, E, E, T, T] [([F, E, F, E, E, E, E, E, T, F, E, E, E, T, T], [F, F, E, E, E, E, E, E, T, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_119 trivial)

theorem z_670 : le (tf [F, E, E, F, E, E, E, T, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, E, F, E, E, T, E, T] [([F, E, E, F, E, E, E, E, T, F, E, E, T, E, T], [F, E, F, E, E, E, E, E, T, F, E, E, T, E, T]), ([F, E, E, F, E, E, E, T, E, F, E, E, E, T, T], [F, E, F, E, E, E, E, T, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_661 (And.intro z_669 trivial))

theorem z_671 : le (tf [F, E, E, E, F, E, E, T, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, F, E, E, T, T, E] [([F, E, E, E, F, E, E, E, T, F, E, E, T, T, E], [F, E, E, F, E, E, E, E, T, F, E, E, T, T, E]), ([F, E, E, E, F, E, E, T, E, F, E, E, T, E, T], [F, E, E, F, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_662 (And.intro z_670 trivial))

theorem z_672 : le (tf [F, E, E, E, F, E, E, T, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, F, E, T, E, E, T] [([F, E, E, E, F, E, E, E, T, F, E, T, E, E, T], [F, E, E, F, E, E, E, E, T, F, E, T, E, E, T]), ([F, E, E, E, F, E, E, T, E, F, E, E, T, E, T], [F, E, E, F, E, E, E, T, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_663 (And.intro z_670 trivial))

theorem z_673 : le (tf [F, E, E, E, E, F, E, T, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, F, E, T, E, T, E] [([F, E, E, E, E, F, E, E, T, F, E, T, E, T, E], [F, E, E, E, F, E, E, E, T, F, E, T, E, T, E]), ([F, E, E, E, E, F, E, T, E, F, E, E, T, T, E], [F, E, E, E, F, E, E, T, E, F, E, E, T, T, E]), ([F, E, E, E, E, F, E, T, E, F, E, T, E, E, T], [F, E, E, E, F, E, E, T, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_664 (And.intro z_671 (And.intro z_672 trivial)))

theorem z_674 : le (tf [F, E, E, E, E, E, F, T, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, F, E, T, T, E, E] [([F, E, E, E, E, E, F, E, T, F, E, T, T, E, E], [F, E, E, E, E, F, E, E, T, F, E, T, T, E, E]), ([F, E, E, E, E, E, F, T, E, F, E, T, E, T, E], [F, E, E, E, E, F, E, T, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_665 (And.intro z_673 trivial))

theorem z_675 : le (tf [F, E, E, E, E, F, E, T, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, F, T, E, E, E, T] [([F, E, E, E, E, F, E, E, T, F, T, E, E, E, T], [F, E, E, E, F, E, E, E, T, F, T, E, E, E, T]), ([F, E, E, E, E, F, E, T, E, F, E, T, E, E, T], [F, E, E, E, F, E, E, T, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_666 (And.intro z_672 trivial))

theorem z_676 : le (tf [F, E, E, E, E, E, F, T, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, F, T, E, E, T, E] [([F, E, E, E, E, E, F, E, T, F, T, E, E, T, E], [F, E, E, E, E, F, E, E, T, F, T, E, E, T, E]), ([F, E, E, E, E, E, F, T, E, F, E, T, E, T, E], [F, E, E, E, E, F, E, T, E, F, E, T, E, T, E]), ([F, E, E, E, E, E, F, T, E, F, T, E, E, E, T], [F, E, E, E, E, F, E, T, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_667 (And.intro z_673 (And.intro z_675 trivial)))

theorem z_677 : le (tf [E, F, E, E, E, E, F, T, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, F, T, E, F, T, E, T, E, E] [([E, F, E, E, E, E, F, E, T, F, T, E, T, E, E], [F, E, E, E, E, E, F, E, T, F, T, E, T, E, E]), ([E, F, E, E, E, E, F, T, E, F, E, T, T, E, E], [F, E, E, E, E, E, F, T, E, F, E, T, T, E, E]), ([E, F, E, E, E, E, F, T, E, F, T, E, E, T, E], [F, E, E, E, E, E, F, T, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_668 (And.intro z_674 (And.intro z_676 trivial)))

theorem z_678 : le (tf [F, E, E, E, E, E, F, T, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, T, F, E, E, E, E, T] [([F, E, E, E, E, E, F, T, E, F, T, E, E, E, T], [F, E, E, E, E, F, E, T, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_675 trivial)

theorem z_679 : le (tf [E, F, E, E, E, E, F, T, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, F, T, T, F, E, E, E, T, E] [([E, F, E, E, E, E, F, T, E, F, T, E, E, T, E], [F, E, E, E, E, E, F, T, E, F, T, E, E, T, E]), ([E, F, E, E, E, E, F, T, T, F, E, E, E, E, T], [F, E, E, E, E, E, F, T, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_676 (And.intro z_678 trivial))

theorem z_680 : le (tf [E, E, F, E, E, E, F, T, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, F, T, T, F, E, E, T, E, E] [([E, E, F, E, E, E, F, T, E, F, T, E, T, E, E], [E, F, E, E, E, E, F, T, E, F, T, E, T, E, E]), ([E, E, F, E, E, E, F, T, T, F, E, E, E, T, E], [E, F, E, E, E, E, F, T, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_677 (And.intro z_679 trivial))

theorem z_681 : le (tf [F, E, E, F, E, E, T, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, T, E, E, F, E, E, T, T, E] [([F, E, E, F, E, E, E, T, E, F, E, E, T, T, E], [F, E, F, E, E, E, E, T, E, F, E, E, T, T, E]), ([F, E, E, F, E, E, T, E, E, F, E, E, T, E, T], [F, E, F, E, E, E, T, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_357 (And.intro z_465 trivial))

theorem z_682 : le (tf [F, E, F, E, E, T, E, E, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, E, E, F, E, E, E, T, T] [([F, E, F, E, E, E, T, E, E, F, E, E, E, T, T], [F, F, E, E, E, E, T, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 trivial)

theorem z_683 : le (tf [F, E, E, F, E, T, E, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, E, E, F, E, E, T, E, T] [([F, E, E, F, E, E, T, E, E, F, E, E, T, E, T], [F, E, F, E, E, E, T, E, E, F, E, E, T, E, T]), ([F, E, E, F, E, T, E, E, E, F, E, E, E, T, T], [F, E, F, E, E, T, E, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_465 (And.intro z_682 trivial))

theorem z_684 : le (tf [F, E, E, E, F, T, E, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, F, E, E, T, T, E] [([F, E, E, E, F, E, T, E, E, F, E, E, T, T, E], [F, E, E, F, E, E, T, E, E, F, E, E, T, T, E]), ([F, E, E, E, F, T, E, E, E, F, E, E, T, E, T], [F, E, E, F, E, T, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_681 (And.intro z_683 trivial))

theorem z_685 : le (tf [F, E, E, E, F, T, E, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, F, E, T, E, E, T] [([F, E, E, E, F, E, T, E, E, F, E, T, E, E, T], [F, E, E, F, E, E, T, E, E, F, E, T, E, E, T]), ([F, E, E, E, F, T, E, E, E, F, E, E, T, E, T], [F, E, E, F, E, T, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_466 (And.intro z_683 trivial))

theorem z_686 : le (tf [F, E, E, E, E, T, F, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, F, E, T, E, T, E] [([F, E, E, E, E, E, F, T, E, F, E, T, E, T, E], [F, E, E, E, E, F, E, T, E, F, E, T, E, T, E]), ([F, E, E, E, E, T, F, E, E, F, E, E, T, T, E], [F, E, E, E, F, T, E, E, E, F, E, E, T, T, E]), ([F, E, E, E, E, T, F, E, E, F, E, T, E, E, T], [F, E, E, E, F, T, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_673 (And.intro z_684 (And.intro z_685 trivial)))

theorem z_687 : le (tf [E, F, E, E, E, T, F, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, F, E, T, T, E, E] [([E, F, E, E, E, E, F, T, E, F, E, T, T, E, E], [F, E, E, E, E, E, F, T, E, F, E, T, T, E, E]), ([E, F, E, E, E, T, F, E, E, F, E, T, E, T, E], [F, E, E, E, E, T, F, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_674 (And.intro z_686 trivial))

theorem z_688 : le (tf [F, E, E, E, E, T, F, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, F, T, E, E, E, T] [([F, E, E, E, E, E, F, T, E, F, T, E, E, E, T], [F, E, E, E, E, F, E, T, E, F, T, E, E, E, T]), ([F, E, E, E, E, T, F, E, E, F, E, T, E, E, T], [F, E, E, E, F, T, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_675 (And.intro z_685 trivial))

theorem z_689 : le (tf [E, F, E, E, E, T, F, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, F, T, E, E, T, E] [([E, F, E, E, E, E, F, T, E, F, T, E, E, T, E], [F, E, E, E, E, E, F, T, E, F, T, E, E, T, E]), ([E, F, E, E, E, T, F, E, E, F, E, T, E, T, E], [F, E, E, E, E, T, F, E, E, F, E, T, E, T, E]), ([E, F, E, E, E, T, F, E, E, F, T, E, E, E, T], [F, E, E, E, E, T, F, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_676 (And.intro z_686 (And.intro z_688 trivial)))

theorem z_690 : le (tf [E, E, F, E, E, T, F, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, F, E, E, F, T, E, T, E, E] [([E, E, F, E, E, E, F, T, E, F, T, E, T, E, E], [E, F, E, E, E, E, F, T, E, F, T, E, T, E, E]), ([E, E, F, E, E, T, F, E, E, F, E, T, T, E, E], [E, F, E, E, E, T, F, E, E, F, E, T, T, E, E]), ([E, E, F, E, E, T, F, E, E, F, T, E, E, T, E], [E, F, E, E, E, T, F, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_677 (And.intro z_687 (And.intro z_689 trivial)))

theorem z_691 : le (tf [E, F, E, E, E, T, F, E, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, T, F, E, E, E, E, T] [([E, F, E, E, E, E, F, T, T, F, E, E, E, E, T], [F, E, E, E, E, E, F, T, T, F, E, E, E, E, T]), ([E, F, E, E, E, T, F, E, E, F, T, E, E, E, T], [F, E, E, E, E, T, F, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_678 (And.intro z_688 trivial))

theorem z_692 : le (tf [E, E, F, E, E, T, F, E, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, F, E, T, F, E, E, E, T, E] [([E, E, F, E, E, E, F, T, T, F, E, E, E, T, E], [E, F, E, E, E, E, F, T, T, F, E, E, E, T, E]), ([E, E, F, E, E, T, F, E, E, F, T, E, E, T, E], [E, F, E, E, E, T, F, E, E, F, T, E, E, T, E]), ([E, E, F, E, E, T, F, E, T, F, E, E, E, E, T], [E, F, E, E, E, T, F, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_679 (And.intro z_689 (And.intro z_691 trivial)))

theorem z_693 : le (tf [E, E, E, F, E, T, F, E, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, F, E, T, F, E, E, T, E, E] [([E, E, E, F, E, E, F, T, T, F, E, E, T, E, E], [E, E, F, E, E, E, F, T, T, F, E, E, T, E, E]), ([E, E, E, F, E, T, F, E, E, F, T, E, T, E, E], [E, E, F, E, E, T, F, E, E, F, T, E, T, E, E]), ([E, E, E, F, E, T, F, E, T, F, E, E, E, T, E], [E, E, F, E, E, T, F, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_680 (And.intro z_690 (And.intro z_692 trivial)))

theorem z_694 : le (tf [F, E, E, E, F, E, T, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, F, E, T, E, T, E] [([F, E, E, E, F, E, E, T, E, F, E, T, E, T, E], [F, E, E, F, E, E, E, T, E, F, E, T, E, T, E]), ([F, E, E, E, F, E, T, E, E, F, E, E, T, T, E], [F, E, E, F, E, E, T, E, E, F, E, E, T, T, E]), ([F, E, E, E, F, E, T, E, E, F, E, T, E, E, T], [F, E, E, F, E, E, T, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 (And.intro z_681 (And.intro z_466 trivial)))

theorem z_695 : le (tf [F, E, E, F, T, E, E, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, T, E, E, E, E, F, E, E, T, T, E] [([F, E, E, F, E, T, E, E, E, F, E, E, T, T, E], [F, E, E, F, E, T, E, E, F, E, E, E, T, T, E]), ([F, E, E, F, T, E, E, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_386 (And.intro z_469 trivial))

theorem z_696 : le (tf [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E] [([F, E, E, E, E, F, T, E, E, F, E, T, E, T, E], [F, E, E, E, F, E, T, E, E, F, E, T, E, T, E]), ([F, E, E, E, T, F, E, E, E, F, E, E, T, T, E], [F, E, E, F, T, E, E, E, E, F, E, E, T, T, E]), ([F, E, E, E, T, F, E, E, E, F, E, T, E, E, T], [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_694 (And.intro z_695 (And.intro z_470 trivial)))

theorem z_697 : le (tf [F, E, E, E, T, E, F, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, F, E, T, T, E, E] [([F, E, E, E, E, T, F, E, E, F, E, T, T, E, E], [F, E, E, E, E, T, F, E, F, E, E, T, T, E, E]), ([F, E, E, E, T, E, F, E, E, F, E, T, E, T, E], [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_696 trivial))

theorem z_698 : le (tf [F, E, E, E, T, E, F, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, F, T, E, E, T, E] [([F, E, E, E, E, T, F, E, E, F, T, E, E, T, E], [F, E, E, E, E, T, F, E, F, E, T, E, E, T, E]), ([F, E, E, E, T, E, F, E, E, F, E, T, E, T, E], [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E]), ([F, E, E, E, T, E, F, E, E, F, T, E, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_398 (And.intro z_696 (And.intro z_471 trivial)))

theorem z_699 : le (tf [E, F, E, E, T, E, F, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, F, T, E, T, E, E] [([E, F, E, E, E, T, F, E, E, F, T, E, T, E, E], [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E]), ([E, F, E, E, T, E, F, E, E, F, E, T, T, E, E], [F, E, E, E, T, E, F, E, E, F, E, T, T, E, E]), ([E, F, E, E, T, E, F, E, E, F, T, E, E, T, E], [F, E, E, E, T, E, F, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 (And.intro z_697 (And.intro z_698 trivial)))

theorem z_700 : le (tf [F, E, F, T, E, E, E, E, E, F, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, T, E, E, E, E, E, F, E, E, E, T, T] [([F, E, F, E, T, E, E, E, E, F, E, E, E, T, T], [F, F, E, E, T, E, E, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_468 trivial)

theorem z_701 : le (tf [F, E, E, T, F, E, E, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, F, E, E, T, E, T] [([F, E, E, E, F, T, E, E, E, F, E, E, T, E, T], [F, E, E, F, E, T, E, E, E, F, E, E, T, E, T]), ([F, E, E, T, F, E, E, E, E, F, E, E, E, T, T], [F, E, F, T, E, E, E, E, E, F, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_683 (And.intro z_700 trivial))

theorem z_702 : le (tf [F, E, E, T, E, F, E, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, F, E, E, T, T, E] [([F, E, E, E, T, F, E, E, E, F, E, E, T, T, E], [F, E, E, F, T, E, E, E, E, F, E, E, T, T, E]), ([F, E, E, T, E, F, E, E, E, F, E, E, T, E, T], [F, E, E, T, F, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_695 (And.intro z_701 trivial))

theorem z_703 : le (tf [F, E, E, T, E, F, E, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, F, E, T, E, E, T] [([F, E, E, E, T, F, E, E, E, F, E, T, E, E, T], [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T]), ([F, E, E, T, E, F, E, E, E, F, E, E, T, E, T], [F, E, E, T, F, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_470 (And.intro z_701 trivial))

theorem z_704 : le (tf [F, E, E, T, E, E, F, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, F, E, T, E, T, E] [([F, E, E, E, T, E, F, E, E, F, E, T, E, T, E], [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E]), ([F, E, E, T, E, E, F, E, E, F, E, E, T, T, E], [F, E, E, T, E, F, E, E, E, F, E, E, T, T, E]), ([F, E, E, T, E, E, F, E, E, F, E, T, E, E, T], [F, E, E, T, E, F, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_696 (And.intro z_702 (And.intro z_703 trivial)))

theorem z_705 : le (tf [E, F, E, T, E, E, F, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, F, E, T, T, E, E] [([E, F, E, E, T, E, F, E, E, F, E, T, T, E, E], [F, E, E, E, T, E, F, E, E, F, E, T, T, E, E]), ([E, F, E, T, E, E, F, E, E, F, E, T, E, T, E], [F, E, E, T, E, E, F, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_697 (And.intro z_704 trivial))

theorem z_706 : le (tf [F, E, E, T, E, E, F, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, F, T, E, E, E, T] [([F, E, E, E, T, E, F, E, E, F, T, E, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T]), ([F, E, E, T, E, E, F, E, E, F, E, T, E, E, T], [F, E, E, T, E, F, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_471 (And.intro z_703 trivial))

theorem z_707 : le (tf [E, F, E, T, E, E, F, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, F, T, E, E, T, E] [([E, F, E, E, T, E, F, E, E, F, T, E, E, T, E], [F, E, E, E, T, E, F, E, E, F, T, E, E, T, E]), ([E, F, E, T, E, E, F, E, E, F, E, T, E, T, E], [F, E, E, T, E, E, F, E, E, F, E, T, E, T, E]), ([E, F, E, T, E, E, F, E, E, F, T, E, E, E, T], [F, E, E, T, E, E, F, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_698 (And.intro z_704 (And.intro z_706 trivial)))

theorem z_708 : le (tf [E, E, F, T, E, E, F, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, F, E, E, F, T, E, T, E, E] [([E, E, F, E, T, E, F, E, E, F, T, E, T, E, E], [E, F, E, E, T, E, F, E, E, F, T, E, T, E, E]), ([E, E, F, T, E, E, F, E, E, F, E, T, T, E, E], [E, F, E, T, E, E, F, E, E, F, E, T, T, E, E]), ([E, E, F, T, E, E, F, E, E, F, T, E, E, T, E], [E, F, E, T, E, E, F, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_699 (And.intro z_705 (And.intro z_707 trivial)))

theorem z_709 : le (tf [F, E, E, E, F, E, E, T, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, F, E, E, E, E, T] [([F, E, E, E, F, E, E, T, E, F, T, E, E, E, T], [F, E, E, F, E, E, E, T, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 trivial)

theorem z_710 : le (tf [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E] [([F, E, E, E, E, F, E, T, E, F, T, E, E, T, E], [F, E, E, E, F, E, E, T, E, F, T, E, E, T, E]), ([F, E, E, E, E, F, E, T, T, F, E, E, E, E, T], [F, E, E, E, F, E, E, T, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_362 (And.intro z_709 trivial))

theorem z_711 : le (tf [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E] [([F, E, E, E, E, F, E, T, E, F, T, E, E, T, E], [F, E, E, E, F, E, E, T, E, F, T, E, E, T, E]), ([F, E, E, E, E, F, T, E, E, F, E, T, E, T, E], [F, E, E, E, F, E, T, E, E, F, E, T, E, T, E]), ([F, E, E, E, E, F, T, E, E, F, T, E, E, E, T], [F, E, E, E, F, E, T, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_362 (And.intro z_694 (And.intro z_467 trivial)))

theorem z_712 : le (tf [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T] [([F, E, E, E, E, F, E, T, T, F, E, E, E, E, T], [F, E, E, E, F, E, E, T, T, F, E, E, E, E, T]), ([F, E, E, E, E, F, T, E, E, F, T, E, E, E, T], [F, E, E, E, F, E, T, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_709 (And.intro z_467 trivial))

theorem z_713 : le (tf [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E] [([E, F, E, E, E, F, E, T, T, F, E, E, E, T, E], [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E]), ([E, F, E, E, E, F, T, E, E, F, T, E, E, T, E], [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E]), ([E, F, E, E, E, F, T, E, T, F, E, E, E, E, T], [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_710 (And.intro z_711 (And.intro z_712 trivial)))

theorem z_714 : le (tf [E, F, E, E, T, F, E, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, F, T, E, E, T, E] [([E, F, E, E, E, F, T, E, E, F, T, E, E, T, E], [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E]), ([E, F, E, E, T, F, E, E, E, F, E, T, E, T, E], [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E]), ([E, F, E, E, T, F, E, E, E, F, T, E, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_711 (And.intro z_696 (And.intro z_471 trivial)))

theorem z_715 : le (tf [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T] [([E, F, E, E, E, F, T, E, T, F, E, E, E, E, T], [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T]), ([E, F, E, E, T, F, E, E, E, F, T, E, E, E, T], [F, E, E, E, T, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_712 (And.intro z_471 trivial))

theorem z_716 : le (tf [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E] [([E, E, F, E, E, F, T, E, T, F, E, E, E, T, E], [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E]), ([E, E, F, E, T, F, E, E, E, F, T, E, E, T, E], [E, F, E, E, T, F, E, E, E, F, T, E, E, T, E]), ([E, E, F, E, T, F, E, E, T, F, E, E, E, E, T], [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_713 (And.intro z_714 (And.intro z_715 trivial)))

theorem z_717 : le (tf [E, F, E, T, E, E, F, E, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, T, F, E, E, E, E, T] [([E, F, E, E, T, E, F, E, T, F, E, E, E, E, T], [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T]), ([E, F, E, T, E, E, F, E, E, F, T, E, E, E, T], [F, E, E, T, E, E, F, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_715 (And.intro z_706 trivial))

theorem z_718 : le (tf [E, E, F, T, E, E, F, E, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, F, E, T, F, E, E, E, T, E] [([E, E, F, E, T, E, F, E, T, F, E, E, E, T, E], [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E]), ([E, E, F, T, E, E, F, E, E, F, T, E, E, T, E], [E, F, E, T, E, E, F, E, E, F, T, E, E, T, E]), ([E, E, F, T, E, E, F, E, T, F, E, E, E, E, T], [E, F, E, T, E, E, F, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_716 (And.intro z_707 (And.intro z_717 trivial)))

theorem z_719 : le (tf [E, E, E, T, F, E, F, E, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, F, E, T, F, E, E, T, E, E] [([E, E, E, E, F, T, F, E, T, F, E, E, T, E, E], [E, E, E, F, E, T, F, E, T, F, E, E, T, E, E]), ([E, E, E, T, F, E, F, E, E, F, T, E, T, E, E], [E, E, F, T, E, E, F, E, E, F, T, E, T, E, E]), ([E, E, E, T, F, E, F, E, T, F, E, E, E, T, E], [E, E, F, T, E, E, F, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_693 (And.intro z_708 (And.intro z_718 trivial)))

theorem z_720 : le (tf [F, E, E, E, E, F, T, T, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, E, F, E, E, E, T] [([F, E, E, E, E, F, T, E, T, E, F, E, E, E, T], [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_712 trivial)

theorem z_721 : le (tf [E, F, E, E, E, F, T, T, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, T, E, E, F, E, E, T, E] [([E, F, E, E, E, F, T, E, T, E, F, E, E, T, E], [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E]), ([E, F, E, E, E, F, T, T, E, E, F, E, E, E, T], [F, E, E, E, E, F, T, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_713 (And.intro z_720 trivial))

theorem z_722 : le (tf [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T] [([E, F, E, E, E, F, T, T, E, E, F, E, E, E, T], [F, E, E, E, E, F, T, T, E, E, F, E, E, E, T]), ([E, F, E, E, T, F, E, E, T, E, F, E, E, E, T], [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_720 (And.intro z_715 trivial))

theorem z_723 : le (tf [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E] [([E, E, F, E, E, F, T, T, E, E, F, E, E, T, E], [E, F, E, E, E, F, T, T, E, E, F, E, E, T, E]), ([E, E, F, E, T, F, E, E, T, E, F, E, E, T, E], [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E]), ([E, E, F, E, T, F, E, T, E, E, F, E, E, E, T], [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_721 (And.intro z_716 (And.intro z_722 trivial)))

theorem z_724 : le (tf [E, F, E, T, E, E, F, T, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, T, E, E, F, E, E, E, T] [([E, F, E, E, T, E, F, T, E, E, F, E, E, E, T], [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T]), ([E, F, E, T, E, E, F, E, T, E, F, E, E, E, T], [E, F, E, T, E, E, F, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_722 (And.intro z_717 trivial))

theorem z_725 : le (tf [E, E, F, T, E, E, F, T, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, F, T, E, E, F, E, E, T, E] [([E, E, F, E, T, E, F, T, E, E, F, E, E, T, E], [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E]), ([E, E, F, T, E, E, F, E, T, E, F, E, E, T, E], [E, E, F, T, E, E, F, E, T, F, E, E, E, T, E]), ([E, E, F, T, E, E, F, T, E, E, F, E, E, E, T], [E, F, E, T, E, E, F, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_723 (And.intro z_718 (And.intro z_724 trivial)))

theorem z_726 : le (tf [E, E, E, T, F, E, F, T, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, F, T, E, E, F, E, T, E, E] [([E, E, E, E, F, T, F, T, E, E, F, E, T, E, E], [E, E, E, F, E, T, F, T, E, E, F, E, T, E, E]), ([E, E, E, T, F, E, F, E, T, E, F, E, T, E, E], [E, E, E, T, F, E, F, E, T, F, E, E, T, E, E]), ([E, E, E, T, F, E, F, T, E, E, F, E, E, T, E], [E, E, F, T, E, E, F, T, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_656 (And.intro z_719 (And.intro z_725 trivial)))

theorem z_727 : le (tf [E, E, E, T, F, E, E, T, F, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, F, E, F, T, E, E, E] [([E, E, E, E, F, T, E, T, F, E, F, T, E, E, E], [E, E, E, F, E, T, E, T, F, E, F, T, E, E, E]), ([E, E, E, T, F, E, E, E, F, T, F, T, E, E, E], [E, E, F, T, E, E, E, E, F, T, F, T, E, E, E]), ([E, E, E, T, F, E, E, T, F, E, F, E, T, E, E], [E, E, E, T, F, E, F, T, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_623 (And.intro z_646 (And.intro z_726 trivial)))

theorem z_728 : le (tf [E, E, E, T, F, E, E, T, F, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, F, E, T, E, F, E, E] [([E, E, E, E, F, T, E, T, F, E, T, E, F, E, E], [E, E, E, F, E, T, E, T, F, E, T, E, F, E, E]), ([E, E, E, T, F, E, E, E, F, T, T, E, F, E, E], [E, E, F, T, E, E, E, E, F, T, T, E, F, E, E]), ([E, E, E, T, F, E, E, T, F, E, E, T, F, E, E], [E, E, E, T, F, E, E, T, F, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_581 (And.intro z_595 (And.intro z_727 trivial)))

theorem z_729 : le (tf [E, E, E, T, F, E, E, T, F, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, F, T, E, E, E, F, E] [([E, E, E, E, F, T, E, T, F, T, E, E, E, F, E], [E, E, E, F, E, T, E, T, F, T, E, E, E, F, E]), ([E, E, E, T, F, E, E, T, F, E, T, E, E, F, E], [E, E, E, T, F, E, E, T, F, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_560 (And.intro z_728 trivial))

theorem z_730 : le (tf [F, E, E, E, E, E, T, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, E, T, E, E, F] [([F, E, E, E, E, E, T, F, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F]), ([F, E, E, E, E, E, T, F, T, E, E, E, T, E, F], [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_150 trivial))

theorem z_731 : le (tf [E, F, E, E, E, E, T, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, E, T, E, E, E, F] [([E, F, E, E, E, E, T, F, E, T, T, E, E, E, F], [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F]), ([E, F, E, E, E, E, T, F, T, E, E, T, E, E, F], [F, E, E, E, E, E, T, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_730 trivial))

theorem z_732 : le (tf [E, F, E, E, E, T, E, F, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, E, T, T, E, E, E, F] [([E, F, E, E, E, E, T, F, E, T, T, E, E, E, F], [F, E, E, E, E, E, T, F, E, T, T, E, E, E, F]), ([E, F, E, E, E, T, E, F, E, T, E, T, E, E, F], [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_423 trivial))

theorem z_733 : le (tf [E, F, E, E, E, T, E, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, E, E, T, E, E, F] [([E, F, E, E, E, E, T, F, T, E, E, T, E, E, F], [F, E, E, E, E, E, T, F, T, E, E, T, E, E, F]), ([E, F, E, E, E, T, E, F, E, T, E, T, E, E, F], [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F]), ([E, F, E, E, E, T, E, F, T, E, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_730 (And.intro z_423 (And.intro z_249 trivial)))

theorem z_734 : le (tf [E, E, F, E, E, T, E, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, T, E, T, E, E, E, F] [([E, E, F, E, E, E, T, F, T, E, T, E, E, E, F], [E, F, E, E, E, E, T, F, T, E, T, E, E, E, F]), ([E, E, F, E, E, T, E, F, E, T, T, E, E, E, F], [E, F, E, E, E, T, E, F, E, T, T, E, E, E, F]), ([E, E, F, E, E, T, E, F, T, E, E, T, E, E, F], [E, F, E, E, E, T, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_731 (And.intro z_732 (And.intro z_733 trivial)))

theorem z_735 : le (tf [E, F, E, E, E, T, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, E, E, T, E, F] [([E, F, E, E, E, T, E, F, T, E, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F]), ([E, F, E, E, E, T, T, F, E, E, E, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_545 trivial))

theorem z_736 : le (tf [E, E, F, E, E, T, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, E, E, T, E, E, F] [([E, E, F, E, E, T, E, F, T, E, E, T, E, E, F], [E, F, E, E, E, T, E, F, T, E, E, T, E, E, F]), ([E, E, F, E, E, T, T, F, E, E, E, E, T, E, F], [E, F, E, E, E, T, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_733 (And.intro z_735 trivial))

theorem z_737 : le (tf [E, E, E, F, E, T, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, E, T, E, E, E, F] [([E, E, E, F, E, T, E, F, T, E, T, E, E, E, F], [E, E, F, E, E, T, E, F, T, E, T, E, E, E, F]), ([E, E, E, F, E, T, T, F, E, E, E, T, E, E, F], [E, E, F, E, E, T, T, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_734 (And.intro z_736 trivial))

theorem z_738 : le (tf [F, E, E, E, T, E, E, F, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, T, E, E, E, F] [([F, E, E, E, E, T, E, F, E, T, T, E, E, E, F], [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F]), ([F, E, E, E, T, E, E, F, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_410 (And.intro z_479 trivial))

theorem z_739 : le (tf [E, F, E, E, T, E, E, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, T, E, E, E, F] [([E, F, E, E, E, T, E, F, T, E, T, E, E, E, F], [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F]), ([E, F, E, E, T, E, E, F, E, T, T, E, E, E, F], [F, E, E, E, T, E, E, F, E, T, T, E, E, E, F]), ([E, F, E, E, T, E, E, F, T, E, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 (And.intro z_738 (And.intro z_484 trivial)))

theorem z_740 : le (tf [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E] [([F, E, E, E, T, E, E, F, E, E, T, T, E, F, E], [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]), ([F, E, E, T, E, E, E, F, E, E, T, E, T, F, E], [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_474 (And.intro z_513 trivial))

theorem z_741 : le (tf [F, E, E, T, E, E, E, F, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, T, E, E, F] [([F, E, E, E, T, E, E, F, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F]), ([F, E, E, T, E, E, E, F, E, E, T, T, E, E, F], [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E]), ([F, E, E, T, E, E, E, F, E, T, E, E, T, E, F], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_740 (And.intro z_517 trivial)))

theorem z_742 : le (tf [E, F, E, T, E, E, E, F, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, T, T, E, E, E, F] [([E, F, E, E, T, E, E, F, E, T, T, E, E, E, F], [F, E, E, E, T, E, E, F, E, T, T, E, E, E, F]), ([E, F, E, T, E, E, E, F, E, T, E, T, E, E, F], [F, E, E, T, E, E, E, F, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_738 (And.intro z_741 trivial))

theorem z_743 : le (tf [E, F, E, T, E, E, E, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, T, E, E, T, E, E, F] [([E, F, E, E, T, E, E, F, T, E, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F]), ([E, F, E, T, E, E, E, F, E, T, E, T, E, E, F], [F, E, E, T, E, E, E, F, E, T, E, T, E, E, F]), ([E, F, E, T, E, E, E, F, T, E, E, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 (And.intro z_741 (And.intro z_525 trivial)))

theorem z_744 : le (tf [E, E, F, T, E, E, E, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, F, T, E, T, E, E, E, F] [([E, E, F, E, T, E, E, F, T, E, T, E, E, E, F], [E, F, E, E, T, E, E, F, T, E, T, E, E, E, F]), ([E, E, F, T, E, E, E, F, E, T, T, E, E, E, F], [E, F, E, T, E, E, E, F, E, T, T, E, E, E, F]), ([E, E, F, T, E, E, E, F, T, E, E, T, E, E, F], [E, F, E, T, E, E, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_739 (And.intro z_742 (And.intro z_743 trivial)))

theorem z_745 : le (tf [F, E, E, E, E, F, E, T, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, E, E, F, E, T] [([F, E, E, E, E, F, E, T, E, T, E, E, F, E, T], [F, E, E, E, F, E, E, T, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_180 trivial)

theorem z_746 : le (tf [F, E, E, E, E, T, F, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, T, E, E, E, F, E, T] [([F, E, E, E, E, E, F, T, T, E, E, E, F, E, T], [F, E, E, E, E, F, E, T, T, E, E, E, F, E, T]), ([F, E, E, E, E, T, F, E, E, T, E, E, F, E, T], [F, E, E, E, F, T, E, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_745 (And.intro z_582 trivial))

theorem z_747 : le (tf [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T] [([F, E, E, E, E, T, E, F, T, E, E, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_746 trivial)

theorem z_748 : le (tf [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E] [([F, E, E, E, E, T, E, F, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([F, E, E, E, E, T, T, F, E, E, E, E, E, F, T], [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_747 trivial))

theorem z_749 : le (tf [F, E, E, E, E, T, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, T, E, E, F] [([F, E, E, E, E, T, E, F, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F]), ([F, E, E, E, E, T, T, F, E, E, E, E, T, E, F], [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 (And.intro z_748 trivial))

theorem z_750 : le (tf [F, E, E, E, E, T, T, F, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, F, E, E, E, T] [([F, E, E, E, E, T, E, F, T, E, F, E, E, E, T], [F, E, E, E, E, T, F, E, T, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_651 trivial)

theorem z_751 : le (tf [F, E, E, E, E, T, T, F, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, E, E, E, F, E, T, E] [([F, E, E, E, E, T, E, F, T, E, E, F, E, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]), ([F, E, E, E, E, T, T, F, E, E, E, F, E, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_750 trivial))

theorem z_752 : le (tf [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T] [([F, E, E, E, E, F, T, E, T, E, E, E, F, E, T], [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T]), ([F, E, E, E, T, F, E, E, E, T, E, E, F, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 (And.intro z_480 trivial))

theorem z_753 : le (tf [F, E, E, E, T, E, F, E, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, E, E, F, T, E] [([F, E, E, E, E, T, F, E, T, E, E, E, F, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]), ([F, E, E, E, T, E, F, E, E, T, E, E, F, T, E], [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E]), ([F, E, E, E, T, E, F, E, T, E, E, E, F, E, T], [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_481 (And.intro z_752 trivial)))

theorem z_754 : le (tf [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T] [([F, E, E, E, E, T, F, E, T, E, E, F, E, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T]), ([F, E, E, E, T, E, F, E, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_428 (And.intro z_480 trivial))

theorem z_755 : le (tf [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T] [([F, E, E, E, E, T, T, F, E, E, E, F, E, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, E, E, T]), ([F, E, E, E, T, E, E, F, T, E, E, F, E, E, T], [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_750 (And.intro z_754 trivial))

theorem z_756 : le (tf [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E] [([F, E, E, E, E, T, T, F, E, E, E, E, F, T, E], [F, E, E, E, E, T, T, F, E, E, E, F, E, T, E]), ([F, E, E, E, T, E, E, F, T, E, E, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, E, E, F, T, E]), ([F, E, E, E, T, E, T, F, E, E, E, E, F, E, T], [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_751 (And.intro z_753 (And.intro z_755 trivial)))

theorem z_757 : le (tf [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F] [([F, E, E, E, E, T, T, F, E, E, E, E, T, E, F], [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E]), ([F, E, E, E, T, E, E, F, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F]), ([F, E, E, E, T, E, T, F, E, E, E, E, E, T, F], [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_748 (And.intro z_483 (And.intro z_756 trivial)))

theorem z_758 : le (tf [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F] [([E, F, E, E, E, T, T, F, E, E, E, T, E, E, F], [F, E, E, E, E, T, T, F, E, E, E, T, E, E, F]), ([E, F, E, E, T, E, E, F, T, E, E, T, E, E, F], [F, E, E, E, T, E, E, F, T, E, E, T, E, E, F]), ([E, F, E, E, T, E, T, F, E, E, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_749 (And.intro z_484 (And.intro z_757 trivial)))

theorem z_759 : le (tf [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F] [([F, E, E, E, T, E, T, F, E, E, E, E, E, T, F], [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E]), ([F, E, E, T, E, E, E, F, T, E, E, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_756 (And.intro z_524 trivial))

theorem z_760 : le (tf [E, F, E, T, E, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, E, E, T, E, F] [([E, F, E, E, T, E, T, F, E, E, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F]), ([E, F, E, T, E, E, E, F, T, E, E, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F]), ([E, F, E, T, E, E, T, F, E, E, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_757 (And.intro z_525 (And.intro z_759 trivial)))

theorem z_761 : le (tf [E, E, F, T, E, E, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, T, F, E, E, E, T, E, E, F] [([E, E, F, E, T, E, T, F, E, E, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F]), ([E, E, F, T, E, E, E, F, T, E, E, T, E, E, F], [E, F, E, T, E, E, E, F, T, E, E, T, E, E, F]), ([E, E, F, T, E, E, T, F, E, E, E, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_758 (And.intro z_743 (And.intro z_760 trivial)))

theorem z_762 : le (tf [E, E, E, T, F, E, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, E, T, E, E, E, F] [([E, E, E, E, F, T, T, F, E, E, T, E, E, E, F], [E, E, E, F, E, T, T, F, E, E, T, E, E, E, F]), ([E, E, E, T, F, E, E, F, T, E, T, E, E, E, F], [E, E, F, T, E, E, E, F, T, E, T, E, E, E, F]), ([E, E, E, T, F, E, T, F, E, E, E, T, E, E, F], [E, E, F, T, E, E, T, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_737 (And.intro z_744 (And.intro z_761 trivial)))

theorem z_763 : le (tf [E, E, E, T, F, E, T, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, E, F, T, E, E, E, E, F] [([E, E, E, E, F, T, T, E, F, T, E, E, E, E, F], [E, E, E, F, E, T, T, E, F, T, E, E, E, E, F]), ([E, E, E, T, F, E, E, T, F, T, E, E, E, E, F], [E, E, E, T, F, E, E, T, F, T, E, E, E, F, E]), ([E, E, E, T, F, E, T, E, F, E, T, E, E, E, F], [E, E, E, T, F, E, T, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_549 (And.intro z_729 (And.intro z_762 trivial)))

theorem z_764 : le (tf [E, E, E, T, F, E, T, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, E, T, E, F, E, E, E, F] [([E, E, E, E, F, T, T, E, T, E, F, E, E, E, F], [E, E, E, F, E, T, T, E, T, E, F, E, E, E, F]), ([E, E, E, T, F, E, E, T, T, E, F, E, E, E, F], [E, E, E, T, F, E, E, T, T, F, E, E, E, E, F]), ([E, E, E, T, F, E, T, E, E, T, F, E, E, E, F], [E, E, E, T, F, E, T, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_453 (And.intro z_540 (And.intro z_763 trivial)))

theorem z_765 : le (tf [E, E, E, T, F, E, T, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, T, E, E, E, F, E, E, F] [([E, E, E, E, F, T, T, T, E, E, E, F, E, E, F], [E, E, E, F, E, T, T, T, E, E, E, F, E, E, F]), ([E, E, E, T, F, E, T, E, T, E, E, F, E, E, F], [E, E, E, T, F, E, T, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 (And.intro z_764 trivial))

theorem z_766 : le (tf [E, E, E, T, T, F, F, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, E, E, F, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_767 : le (tf [E, E, E, T, T, F, F, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, E, E, T, F, E] [([E, E, E, T, T, F, F, E, E, E, E, E, E, F, T], [E, E, E, T, T, F, F, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_766 trivial)

theorem z_768 : le (tf [E, E, E, T, T, F, F, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, E, T, E, E, F] [([E, E, E, T, T, F, F, E, E, E, E, E, T, E, F], [E, E, E, T, T, F, F, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_767 trivial)

theorem z_769 : le (tf [E, E, E, T, T, F, E, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, F, E, E, T, E, E, E, F] [([E, E, E, T, E, F, T, F, E, E, T, E, E, E, F], [E, E, E, T, F, E, T, F, E, E, T, E, E, E, F]), ([E, E, E, T, T, F, E, F, E, E, E, T, E, E, F], [E, E, E, T, T, F, F, E, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_762 (And.intro z_768 trivial))

theorem z_770 : le (tf [E, E, E, T, T, F, E, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, E, F, T, E, E, E, E, F] [([E, E, E, T, E, F, T, E, F, T, E, E, E, E, F], [E, E, E, T, F, E, T, E, F, T, E, E, E, E, F]), ([E, E, E, T, T, F, E, E, F, E, T, E, E, E, F], [E, E, E, T, T, F, E, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_763 (And.intro z_769 trivial))

theorem z_771 : le (tf [E, E, E, T, T, F, E, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, E, T, E, F, E, E, E, F] [([E, E, E, T, E, F, T, E, T, E, F, E, E, E, F], [E, E, E, T, F, E, T, E, T, E, F, E, E, E, F]), ([E, E, E, T, T, F, E, E, E, T, F, E, E, E, F], [E, E, E, T, T, F, E, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_764 (And.intro z_770 trivial))

theorem z_772 : le (tf [E, E, E, T, T, F, E, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, T, E, E, E, F, E, E, F] [([E, E, E, T, E, F, T, T, E, E, E, F, E, E, F], [E, E, E, T, F, E, T, T, E, E, E, F, E, E, F]), ([E, E, E, T, T, F, E, E, T, E, E, F, E, E, F], [E, E, E, T, T, F, E, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_765 (And.intro z_771 trivial))

theorem z_773 : le (tf [E, E, E, T, T, T, F, E, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, T, F, E, E, E, E, F, E, E, F] [([E, E, E, T, T, E, F, T, E, E, E, F, E, E, F], [E, E, E, T, T, F, E, T, E, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_772 trivial)

theorem z_774 : le (tf [F, E, E, E, T, E, E, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, T, E, F, E, E, F] [([F, E, E, E, E, T, E, E, T, T, E, F, E, E, F], [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F]), ([F, E, E, E, T, E, E, E, T, E, T, F, E, E, F], [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_251 (And.intro z_485 trivial))

theorem z_775 : le (tf [F, E, E, E, F, E, T, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, E, E, E, E, F, T, T] [([F, E, E, E, F, E, E, T, E, E, E, E, F, T, T], [F, E, E, F, E, E, E, T, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_776 : le (tf [F, E, E, E, T, F, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, E, E, F, T, T] [([F, E, E, E, E, F, T, E, E, E, E, E, F, T, T], [F, E, E, E, F, E, T, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_775 trivial)

theorem z_777 : le (tf [F, E, E, E, T, E, F, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, E, T, F, E, T] [([F, E, E, E, E, T, F, E, E, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T]), ([F, E, E, E, T, E, F, E, E, E, E, E, F, T, T], [F, E, E, E, T, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_776 trivial))

theorem z_778 : le (tf [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E] [([F, E, E, E, E, T, E, F, E, E, E, T, F, T, E], [F, E, E, E, E, T, F, E, E, E, E, T, F, T, E]), ([F, E, E, E, T, E, E, F, E, E, E, T, F, E, T], [F, E, E, E, T, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_203 (And.intro z_777 trivial))

theorem z_779 : le (tf [F, E, E, E, T, E, E, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, E, T, T, E, F] [([F, E, E, E, E, T, E, F, E, E, E, T, T, E, F], [F, E, E, E, E, T, F, E, E, E, E, T, T, E, F]), ([F, E, E, E, T, E, E, F, E, E, E, T, E, T, F], [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_204 (And.intro z_778 trivial))

theorem z_780 : le (tf [F, E, E, E, T, E, E, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, T, E, E, T, F] [([F, E, E, E, E, T, E, F, E, E, T, E, E, T, F], [F, E, E, E, E, T, F, E, E, E, T, E, E, T, F]), ([F, E, E, E, T, E, E, F, E, E, E, T, E, T, F], [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_205 (And.intro z_778 trivial))

theorem z_781 : le (tf [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F] [([F, E, E, E, E, T, E, E, F, E, T, E, T, E, F], [F, E, E, E, E, T, E, F, E, E, T, E, T, E, F]), ([F, E, E, E, T, E, E, E, F, E, E, T, T, E, F], [F, E, E, E, T, E, E, F, E, E, E, T, T, E, F]), ([F, E, E, E, T, E, E, E, F, E, T, E, E, T, F], [F, E, E, E, T, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_206 (And.intro z_779 (And.intro z_780 trivial)))

theorem z_782 : le (tf [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F] [([F, E, E, E, E, T, E, F, T, E, E, E, E, T, F], [F, E, E, E, E, T, F, E, T, E, E, E, E, T, F]), ([F, E, E, E, T, E, E, F, E, T, E, E, E, T, F], [F, E, E, E, T, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 (And.intro z_531 trivial))

theorem z_783 : le (tf [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F] [([F, E, E, E, E, T, E, E, T, F, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F]), ([F, E, E, E, T, E, E, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F]), ([F, E, E, E, T, E, E, E, T, F, E, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_781 (And.intro z_782 trivial)))

theorem z_784 : le (tf [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F] [([F, E, E, E, E, T, E, T, E, F, E, E, E, T, F], [F, E, E, E, E, T, E, T, F, E, E, E, E, T, F]), ([F, E, E, E, T, E, E, E, T, F, E, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_439 (And.intro z_782 trivial))

theorem z_785 : le (tf [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F] [([F, E, E, E, E, T, E, T, E, E, F, E, T, E, F], [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F]), ([F, E, E, E, T, E, E, E, T, E, F, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F]), ([F, E, E, E, T, E, E, T, E, E, F, E, E, T, F], [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_440 (And.intro z_783 (And.intro z_784 trivial)))

theorem z_786 : le (tf [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F] [([F, E, E, E, E, T, E, T, E, E, T, F, E, E, F], [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F]), ([F, E, E, E, T, E, E, E, T, E, T, F, E, E, F], [F, E, E, E, T, E, E, E, T, F, T, E, E, E, F]), ([F, E, E, E, T, E, E, T, E, E, E, F, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_435 (And.intro z_485 (And.intro z_785 trivial)))

theorem z_787 : le (tf [F, E, E, E, T, E, E, T, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, T, E, E, F, E, F] [([F, E, E, E, E, T, E, T, E, T, E, E, F, E, F], [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F]), ([F, E, E, E, T, E, E, E, T, T, E, E, F, E, F], [F, E, E, E, T, E, E, E, T, T, E, F, E, E, F]), ([F, E, E, E, T, E, E, T, E, E, T, E, F, E, F], [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_774 (And.intro z_786 trivial)))

theorem z_788 : le (tf [E, F, E, E, T, E, E, T, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, T, E, E, E, F, E, F] [([E, F, E, E, E, T, E, T, T, E, E, E, F, E, F], [E, F, E, E, E, T, E, T, T, E, E, F, E, E, F]), ([E, F, E, E, T, E, E, T, E, T, E, E, F, E, F], [F, E, E, E, T, E, E, T, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_787 trivial))

theorem z_789 : le (tf [F, E, E, E, E, T, T, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, E, E, F, E, T, E, E, F] [([F, E, E, E, E, T, E, T, E, F, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F]), ([F, E, E, E, E, T, T, E, E, F, E, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_546 trivial))

theorem z_790 : le (tf [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F] [([F, E, E, E, E, T, T, E, F, E, E, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F]), ([F, E, E, E, T, E, E, T, F, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_545 (And.intro z_496 trivial))

theorem z_791 : le (tf [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F] [([F, E, E, E, E, T, T, E, E, F, E, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F]), ([F, E, E, E, T, E, E, T, E, F, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F]), ([F, E, E, E, T, E, T, E, E, F, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_546 (And.intro z_497 (And.intro z_790 trivial)))

theorem z_792 : le (tf [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F] [([F, E, E, E, E, T, T, E, E, E, F, T, E, E, F], [F, E, E, E, E, T, T, E, E, F, E, T, E, E, F]), ([F, E, E, E, T, E, E, T, E, E, F, T, E, E, F], [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F]), ([F, E, E, E, T, E, T, E, E, E, F, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_789 (And.intro z_498 (And.intro z_791 trivial)))

theorem z_793 : le (tf [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F] [([F, E, E, E, E, T, T, E, E, E, T, E, F, E, F], [F, E, E, E, E, T, T, E, E, E, T, F, E, E, F]), ([F, E, E, E, T, E, E, T, E, E, T, E, F, E, F], [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F]), ([F, E, E, E, T, E, T, E, E, E, E, T, F, E, F], [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_443 (And.intro z_786 (And.intro z_792 trivial)))

theorem z_794 : le (tf [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F] [([E, F, E, E, E, T, T, E, E, T, E, E, F, E, F], [E, F, E, E, E, T, T, E, E, T, E, F, E, E, F]), ([E, F, E, E, T, E, E, T, E, T, E, E, F, E, F], [F, E, E, E, T, E, E, T, E, T, E, E, F, E, F]), ([E, F, E, E, T, E, T, E, E, E, T, E, F, E, F], [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 (And.intro z_787 (And.intro z_793 trivial)))

theorem z_795 : le (tf [E, E, F, E, T, E, T, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, T, E, E, E, F, E, F] [([E, E, F, E, E, T, T, E, T, E, E, E, F, E, F], [E, E, F, E, E, T, T, E, T, E, E, F, E, E, F]), ([E, E, F, E, T, E, E, T, T, E, E, E, F, E, F], [E, F, E, E, T, E, E, T, T, E, E, E, F, E, F]), ([E, E, F, E, T, E, T, E, E, T, E, E, F, E, F], [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_445 (And.intro z_788 (And.intro z_794 trivial)))

theorem z_796 : le (tf [E, F, E, E, T, E, E, T, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, T, E, F, E, E, F] [([E, F, E, E, E, T, E, T, E, T, E, F, E, E, F], [F, E, E, E, E, T, E, T, E, T, E, F, E, E, F]), ([E, F, E, E, T, E, E, E, T, T, E, F, E, E, F], [F, E, E, E, T, E, E, E, T, T, E, F, E, E, F]), ([E, F, E, E, T, E, E, T, E, E, T, F, E, E, F], [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_774 (And.intro z_786 trivial)))

theorem z_797 : le (tf [E, E, F, E, T, E, E, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, T, E, E, F, E, E, F] [([E, E, F, E, E, T, E, T, T, E, E, F, E, E, F], [E, F, E, E, E, T, E, T, T, E, E, F, E, E, F]), ([E, E, F, E, T, E, E, T, E, T, E, F, E, E, F], [E, F, E, E, T, E, E, T, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_796 trivial))

theorem z_798 : le (tf [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F] [([F, E, E, E, E, T, E, E, F, T, E, T, E, E, F], [F, E, E, E, E, T, E, F, E, T, E, T, E, E, F]), ([F, E, E, E, T, E, E, E, F, E, T, T, E, E, F], [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E]), ([F, E, E, E, T, E, E, E, F, T, E, E, T, E, F], [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_423 (And.intro z_500 (And.intro z_495 trivial)))

theorem z_799 : le (tf [F, E, E, E, T, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, E, F, T, E, E, F] [([F, E, E, E, E, T, E, E, T, E, F, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F]), ([F, E, E, E, T, E, E, E, E, T, F, T, E, E, F], [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F]), ([F, E, E, E, T, E, E, E, T, E, F, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_250 (And.intro z_798 (And.intro z_783 trivial)))

theorem z_800 : le (tf [E, F, E, E, T, E, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, T, T, F, E, E, E, F] [([E, F, E, E, E, T, E, E, T, T, F, E, E, E, F], [F, E, E, E, E, T, E, E, T, T, F, E, E, E, F]), ([E, F, E, E, T, E, E, E, T, E, F, T, E, E, F], [F, E, E, E, T, E, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_251 (And.intro z_799 trivial))

theorem z_801 : le (tf [E, F, E, E, T, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, E, F, T, E, E, F] [([E, F, E, E, E, T, E, T, E, E, F, T, E, E, F], [F, E, E, E, E, T, E, T, E, E, F, T, E, E, F]), ([E, F, E, E, T, E, E, E, T, E, F, T, E, E, F], [F, E, E, E, T, E, E, E, T, E, F, T, E, E, F]), ([E, F, E, E, T, E, E, T, E, E, F, E, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_448 (And.intro z_799 (And.intro z_785 trivial)))

theorem z_802 : le (tf [E, E, F, E, T, E, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, E, T, F, E, E, E, F] [([E, E, F, E, E, T, E, T, E, T, F, E, E, E, F], [E, F, E, E, E, T, E, T, E, T, F, E, E, E, F]), ([E, E, F, E, T, E, E, E, T, T, F, E, E, E, F], [E, F, E, E, T, E, E, E, T, T, F, E, E, E, F]), ([E, E, F, E, T, E, E, T, E, E, F, T, E, E, F], [E, F, E, E, T, E, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_449 (And.intro z_800 (And.intro z_801 trivial)))

theorem z_803 : le (tf [F, E, E, E, E, F, E, T, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, E, T, E, F, T] [([F, E, E, E, E, F, E, E, T, E, E, T, E, F, T], [F, E, E, E, F, E, E, E, T, E, E, T, E, F, T]), ([F, E, E, E, E, F, E, T, E, E, E, E, T, F, T], [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 (And.intro z_48 trivial))

theorem z_804 : le (tf [F, E, E, E, F, T, E, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, E, E, T, F, T] [([F, E, E, E, F, E, T, E, E, E, E, E, T, F, T], [F, E, E, F, E, E, T, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 trivial)

theorem z_805 : le (tf [F, E, E, E, E, T, F, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, E, T, E, F, T] [([F, E, E, E, E, E, F, T, E, E, E, T, E, F, T], [F, E, E, E, E, F, E, T, E, E, E, T, E, F, T]), ([F, E, E, E, E, T, F, E, E, E, E, E, T, F, T], [F, E, E, E, F, T, E, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_803 (And.intro z_804 trivial))

theorem z_806 : le (tf [F, E, E, E, E, T, E, F, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, E, T, T, F, E] [([F, E, E, E, E, E, T, F, E, E, E, T, T, F, E], [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]), ([F, E, E, E, E, T, E, F, E, E, E, T, E, F, T], [F, E, E, E, E, T, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_805 trivial))

theorem z_807 : le (tf [F, E, E, E, E, T, E, F, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, E, E, F, T] [([F, E, E, E, E, E, T, F, E, E, T, E, E, F, T], [F, E, E, E, E, F, T, E, E, E, T, E, E, F, T]), ([F, E, E, E, E, T, E, F, E, E, E, T, E, F, T], [F, E, E, E, E, T, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_805 trivial))

theorem z_808 : le (tf [F, E, E, E, E, T, E, E, F, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, E, T, E, T, F, E] [([F, E, E, E, E, E, T, E, F, E, T, E, T, F, E], [F, E, E, E, E, E, T, F, E, E, T, E, T, F, E]), ([F, E, E, E, E, T, E, E, F, E, E, T, T, F, E], [F, E, E, E, E, T, E, F, E, E, E, T, T, F, E]), ([F, E, E, E, E, T, E, E, F, E, T, E, E, F, T], [F, E, E, E, E, T, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_806 (And.intro z_807 trivial)))

theorem z_809 : le (tf [F, E, E, E, E, T, E, F, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, E, E, F, T] [([F, E, E, E, E, E, T, F, T, E, E, E, E, F, T], [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T]), ([F, E, E, E, E, T, E, F, E, T, E, E, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 (And.intro z_223 trivial))

theorem z_810 : le (tf [F, E, E, E, E, T, E, E, T, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, T, F, E, E, T, F, E] [([F, E, E, E, E, E, T, E, T, F, E, E, T, F, E], [F, E, E, E, E, E, T, F, T, E, E, E, T, F, E]), ([F, E, E, E, E, T, E, E, E, F, T, E, T, F, E], [F, E, E, E, E, T, E, E, F, E, T, E, T, F, E]), ([F, E, E, E, E, T, E, E, T, F, E, E, E, F, T], [F, E, E, E, E, T, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 (And.intro z_808 (And.intro z_809 trivial)))

theorem z_811 : le (tf [F, E, E, E, E, T, E, E, T, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, T, E, F, T, E, F, E] [([F, E, E, E, E, E, T, E, T, E, F, T, E, F, E], [F, E, E, E, E, E, T, E, T, F, E, T, E, F, E]), ([F, E, E, E, E, T, E, E, E, T, F, T, E, F, E], [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E]), ([F, E, E, E, E, T, E, E, T, E, F, E, T, F, E], [F, E, E, E, E, T, E, E, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_151 (And.intro z_554 (And.intro z_810 trivial)))

theorem z_812 : le (tf [E, F, E, E, E, T, E, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, T, T, F, E, E, F, E] [([E, F, E, E, E, E, T, E, T, T, F, E, E, F, E], [F, E, E, E, E, E, T, E, T, T, F, E, E, F, E]), ([E, F, E, E, E, T, E, E, T, E, F, T, E, F, E], [F, E, E, E, E, T, E, E, T, E, F, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_152 (And.intro z_811 trivial))

theorem z_813 : le (tf [F, E, E, E, T, E, E, E, E, T, F, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, E, T, F, T, E, F, E] [([F, E, E, E, E, T, E, E, E, T, F, T, E, F, E], [F, E, E, E, E, T, E, E, F, T, E, T, E, F, E]), ([F, E, E, E, T, E, E, E, E, T, F, E, T, F, E], [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_554 (And.intro z_495 trivial))

theorem z_814 : le (tf [F, E, E, E, T, E, F, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, E, E, T, F, T] [([F, E, E, E, E, T, F, E, E, E, E, E, T, F, T], [F, E, E, E, F, T, E, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_804 trivial)

theorem z_815 : le (tf [F, E, E, E, T, E, E, F, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, E, T, E, F, T] [([F, E, E, E, E, T, E, F, E, E, E, T, E, F, T], [F, E, E, E, E, T, F, E, E, E, E, T, E, F, T]), ([F, E, E, E, T, E, E, F, E, E, E, E, T, F, T], [F, E, E, E, T, E, F, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_805 (And.intro z_814 trivial))

theorem z_816 : le (tf [F, E, E, E, T, E, E, E, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, T, E, E, F, T] [([F, E, E, E, E, T, E, E, F, E, T, E, E, F, T], [F, E, E, E, E, T, E, F, E, E, T, E, E, F, T]), ([F, E, E, E, T, E, E, E, F, E, E, T, E, F, T], [F, E, E, E, T, E, E, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_807 (And.intro z_815 trivial))

theorem z_817 : le (tf [F, E, E, E, T, E, E, E, T, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, F, E, E, E, F, T] [([F, E, E, E, E, T, E, E, T, F, E, E, E, F, T], [F, E, E, E, E, T, E, F, T, E, E, E, E, F, T]), ([F, E, E, E, T, E, E, E, E, F, T, E, E, F, T], [F, E, E, E, T, E, E, E, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_809 (And.intro z_816 trivial))

theorem z_818 : le (tf [F, E, E, E, T, E, E, E, T, E, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, E, F, E, T, F, E] [([F, E, E, E, E, T, E, E, T, E, F, E, T, F, E], [F, E, E, E, E, T, E, E, T, F, E, E, T, F, E]), ([F, E, E, E, T, E, E, E, E, T, F, E, T, F, E], [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E]), ([F, E, E, E, T, E, E, E, T, E, F, E, E, F, T], [F, E, E, E, T, E, E, E, T, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_810 (And.intro z_495 (And.intro z_817 trivial)))

theorem z_819 : le (tf [E, F, E, E, T, E, E, E, T, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, T, E, F, T, E, F, E] [([E, F, E, E, E, T, E, E, T, E, F, T, E, F, E], [F, E, E, E, E, T, E, E, T, E, F, T, E, F, E]), ([E, F, E, E, T, E, E, E, E, T, F, T, E, F, E], [F, E, E, E, T, E, E, E, E, T, F, T, E, F, E]), ([E, F, E, E, T, E, E, E, T, E, F, E, T, F, E], [F, E, E, E, T, E, E, E, T, E, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_811 (And.intro z_813 (And.intro z_818 trivial)))

theorem z_820 : le (tf [E, E, F, E, T, E, E, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, T, T, F, E, E, F, E] [([E, E, F, E, E, T, E, E, T, T, F, E, E, F, E], [E, F, E, E, E, T, E, E, T, T, F, E, E, F, E]), ([E, E, F, E, T, E, E, E, T, E, F, T, E, F, E], [E, F, E, E, T, E, E, E, T, E, F, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_812 (And.intro z_819 trivial))

theorem z_821 : le (tf [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E] [([F, E, E, E, E, E, T, F, T, E, E, T, E, F, E], [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, T, E, F, E], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([F, E, E, E, E, T, E, F, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_349 (And.intro z_409 (And.intro z_419 trivial)))

theorem z_822 : le (tf [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T] [([F, E, E, E, E, T, F, E, T, E, E, E, E, F, T], [F, E, E, E, F, T, E, E, T, E, E, E, E, F, T]), ([F, E, E, E, T, E, F, E, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_418 (And.intro z_477 trivial))

theorem z_823 : le (tf [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E] [([F, E, E, E, E, T, E, F, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([F, E, E, E, T, E, E, F, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]), ([F, E, E, E, T, E, E, F, T, E, E, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_478 (And.intro z_822 trivial)))

theorem z_824 : le (tf [F, E, E, E, T, E, E, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, F, E, T, E, F, E] [([F, E, E, E, E, T, E, E, T, F, E, T, E, F, E], [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E]), ([F, E, E, E, T, E, E, E, E, F, T, T, E, F, E], [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E]), ([F, E, E, E, T, E, E, E, T, F, E, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_821 (And.intro z_500 (And.intro z_823 trivial)))

theorem z_825 : le (tf [F, E, E, T, E, E, E, E, F, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, E, T, E, F, E] [([F, E, E, E, T, E, E, E, F, T, E, T, E, F, E], [F, E, E, E, T, E, E, E, F, T, E, T, F, E, E]), ([F, E, E, T, E, E, E, E, F, E, T, T, E, F, E], [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E]), ([F, E, E, T, E, E, E, E, F, T, E, E, T, F, E], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_589 (And.intro z_740 (And.intro z_517 trivial)))

theorem z_826 : le (tf [F, E, E, T, E, E, E, F, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, E, E, E, F, T] [([F, E, E, E, T, E, E, F, T, E, E, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T]), ([F, E, E, T, E, E, E, F, E, T, E, E, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_822 (And.intro z_516 trivial))

theorem z_827 : le (tf [F, E, E, T, E, E, E, E, T, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, T, F, E, E, T, F, E] [([F, E, E, E, T, E, E, E, T, F, E, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E]), ([F, E, E, T, E, E, E, E, E, F, T, E, T, F, E], [F, E, E, T, E, E, E, E, E, F, T, F, T, E, E]), ([F, E, E, T, E, E, E, E, T, F, E, E, E, F, T], [F, E, E, T, E, E, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_823 (And.intro z_506 (And.intro z_826 trivial)))

theorem z_828 : le (tf [F, E, E, T, E, E, E, E, T, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, T, E, F, T, E, F, E] [([F, E, E, E, T, E, E, E, T, E, F, T, E, F, E], [F, E, E, E, T, E, E, E, T, F, E, T, E, F, E]), ([F, E, E, T, E, E, E, E, E, T, F, T, E, F, E], [F, E, E, T, E, E, E, E, F, T, E, T, E, F, E]), ([F, E, E, T, E, E, E, E, T, E, F, E, T, F, E], [F, E, E, T, E, E, E, E, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_824 (And.intro z_825 (And.intro z_827 trivial)))

theorem z_829 : le (tf [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T] [([F, E, E, T, F, E, E, E, E, E, E, F, E, T, T], [F, E, F, T, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_508 trivial)

theorem z_830 : le (tf [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T] [([F, E, E, T, E, F, E, E, E, E, E, F, T, E, T], [F, E, E, T, F, E, E, E, E, E, E, F, T, E, T]), ([F, E, T, E, E, F, E, E, E, E, E, F, E, T, T], [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_509 (And.intro z_829 trivial))

theorem z_831 : le (tf [F, E, T, E, E, E, F, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, E, E, F, T, T, E] [([F, E, E, T, E, E, F, E, E, E, E, F, T, T, E], [F, E, E, T, E, F, E, E, E, E, E, F, T, T, E]), ([F, E, T, E, E, E, F, E, E, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_510 (And.intro z_830 trivial))

theorem z_832 : le (tf [F, E, T, E, E, E, F, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, E, T, F, E, E, T] [([F, E, E, T, E, E, F, E, E, E, T, F, E, E, T], [F, E, E, T, E, F, E, E, E, E, T, F, E, E, T]), ([F, E, T, E, E, E, F, E, E, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_511 (And.intro z_830 trivial))

theorem z_833 : le (tf [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E] [([F, E, E, T, E, E, E, F, E, E, T, F, E, T, E], [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E]), ([F, E, T, E, E, E, E, F, E, E, E, F, T, T, E], [F, E, T, E, E, E, F, E, E, E, E, F, T, T, E]), ([F, E, T, E, E, E, E, F, E, E, T, F, E, E, T], [F, E, T, E, E, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 (And.intro z_831 (And.intro z_832 trivial)))

theorem z_834 : le (tf [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E] [([F, E, E, T, E, E, E, E, F, E, T, F, T, E, E], [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E]), ([F, E, T, E, E, E, E, E, F, E, T, F, E, T, E], [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_513 (And.intro z_833 trivial))

theorem z_835 : le (tf [F, E, T, E, E, F, E, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, E, T, E, F, T] [([F, E, E, T, E, F, E, E, E, E, E, T, E, F, T], [F, E, E, T, F, E, E, E, E, E, E, T, E, F, T]), ([F, E, T, E, E, F, E, E, E, E, E, E, T, F, T], [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_514 (And.intro z_830 trivial))

theorem z_836 : le (tf [F, E, T, E, E, E, F, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, E, T, E, E, F, T] [([F, E, E, T, E, E, F, E, E, E, T, E, E, F, T], [F, E, E, T, E, F, E, E, E, E, T, E, E, F, T]), ([F, E, T, E, E, E, F, E, E, E, E, T, E, F, T], [F, E, T, E, E, F, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_515 (And.intro z_835 trivial))

theorem z_837 : le (tf [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T] [([F, E, E, T, E, E, E, F, E, T, E, E, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T]), ([F, E, T, E, E, E, E, F, E, E, T, E, E, F, T], [F, E, T, E, E, E, F, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_516 (And.intro z_836 trivial))

theorem z_838 : le (tf [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E] [([F, E, E, T, E, E, E, E, F, T, E, E, T, F, E], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E]), ([F, E, T, E, E, E, E, E, F, E, T, E, T, F, E], [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E]), ([F, E, T, E, E, E, E, E, F, T, E, E, E, F, T], [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_517 (And.intro z_834 (And.intro z_837 trivial)))

theorem z_839 : le (tf [F, E, T, E, E, E, E, E, E, T, F, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, E, T, F, T, E, F, E] [([F, E, E, T, E, E, E, E, E, T, F, T, E, F, E], [F, E, E, T, E, E, E, E, F, T, E, T, E, F, E]), ([F, E, T, E, E, E, E, E, E, T, F, E, T, F, E], [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_825 (And.intro z_838 trivial))

theorem z_840 : le (tf [F, E, E, T, E, E, F, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, E, T, E, F, T] [([F, E, E, E, T, E, F, E, E, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, E, E, T, E, F, T]), ([F, E, E, T, E, E, F, E, E, E, E, E, T, F, T], [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 (And.intro z_502 trivial))

theorem z_841 : le (tf [F, E, E, T, E, E, E, F, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, T, E, E, F, T] [([F, E, E, E, T, E, E, F, E, E, T, E, E, F, T], [F, E, E, E, T, E, F, E, E, E, T, E, E, F, T]), ([F, E, E, T, E, E, E, F, E, E, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_840 trivial))

theorem z_842 : le (tf [F, E, T, E, E, E, F, E, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, E, E, E, T, F, T] [([F, E, E, T, E, E, F, E, E, E, E, E, T, F, T], [F, E, E, T, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 trivial)

theorem z_843 : le (tf [F, E, T, E, E, E, E, F, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, E, T, E, F, T] [([F, E, E, T, E, E, E, F, E, E, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, E, E, T, E, F, T]), ([F, E, T, E, E, E, E, F, E, E, E, E, T, F, T], [F, E, T, E, E, E, F, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_840 (And.intro z_842 trivial))

theorem z_844 : le (tf [F, E, T, E, E, E, E, E, F, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, E, T, E, E, F, T] [([F, E, E, T, E, E, E, E, F, E, T, E, E, F, T], [F, E, E, T, E, E, E, F, E, E, T, E, E, F, T]), ([F, E, T, E, E, E, E, E, F, E, E, T, E, F, T], [F, E, T, E, E, E, E, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_841 (And.intro z_843 trivial))

theorem z_845 : le (tf [F, E, T, E, E, E, E, E, T, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, F, E, E, E, F, T] [([F, E, E, T, E, E, E, E, T, F, E, E, E, F, T], [F, E, E, T, E, E, E, F, T, E, E, E, E, F, T]), ([F, E, T, E, E, E, E, E, E, F, T, E, E, F, T], [F, E, T, E, E, E, E, E, F, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_826 (And.intro z_844 trivial))

theorem z_846 : le (tf [F, E, T, E, E, E, E, E, T, E, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, E, F, E, T, F, E] [([F, E, E, T, E, E, E, E, T, E, F, E, T, F, E], [F, E, E, T, E, E, E, E, T, F, E, E, T, F, E]), ([F, E, T, E, E, E, E, E, E, T, F, E, T, F, E], [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E]), ([F, E, T, E, E, E, E, E, T, E, F, E, E, F, T], [F, E, T, E, E, E, E, E, T, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_827 (And.intro z_838 (And.intro z_845 trivial)))

theorem z_847 : le (tf [E, F, T, E, E, E, E, E, T, E, F, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, T, E, F, T, E, F, E] [([E, F, E, T, E, E, E, E, T, E, F, T, E, F, E], [F, E, E, T, E, E, E, E, T, E, F, T, E, F, E]), ([E, F, T, E, E, E, E, E, E, T, F, T, E, F, E], [F, E, T, E, E, E, E, E, E, T, F, T, E, F, E]), ([E, F, T, E, E, E, E, E, T, E, F, E, T, F, E], [F, E, T, E, E, E, E, E, T, E, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_828 (And.intro z_839 (And.intro z_846 trivial)))

theorem z_848 : le (tf [E, E, T, F, E, E, E, E, T, T, F, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, T, T, F, E, E, F, E] [([E, E, E, F, T, E, E, E, T, T, F, E, E, F, E], [E, E, F, E, T, E, E, E, T, T, F, E, E, F, E]), ([E, E, T, F, E, E, E, E, T, E, F, T, E, F, E], [E, F, T, E, E, E, E, E, T, E, F, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_820 (And.intro z_847 trivial))

theorem z_849 : le (tf [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T] [([F, E, E, T, F, E, E, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, E, E, F, T, E, E, T]), ([F, E, T, E, F, E, E, E, E, E, E, E, F, T, T], [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_520 (And.intro z_829 trivial))

theorem z_850 : le (tf [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E] [([F, E, E, T, E, F, E, E, E, E, E, T, F, T, E], [F, E, E, T, F, E, E, E, E, E, E, T, F, T, E]), ([F, E, T, E, E, F, E, E, E, E, E, T, F, E, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_521 (And.intro z_849 trivial))

theorem z_851 : le (tf [F, E, T, E, E, F, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, T, E, E, T, F] [([F, E, E, T, E, F, E, E, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, E, E, T, E, E, T, F]), ([F, E, T, E, E, F, E, E, E, E, E, T, E, T, F], [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_522 (And.intro z_850 trivial))

theorem z_852 : le (tf [F, E, T, E, E, E, F, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, T, E, E, E, T, F] [([F, E, E, T, E, E, F, E, E, T, E, E, E, T, F], [F, E, E, T, E, F, E, E, E, T, E, E, E, T, F]), ([F, E, T, E, E, E, F, E, E, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 (And.intro z_851 trivial))

theorem z_853 : le (tf [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F] [([F, E, E, T, E, E, E, F, T, E, E, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F]), ([F, E, T, E, E, E, E, F, E, T, E, E, E, T, F], [F, E, T, E, E, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_524 (And.intro z_852 trivial))

theorem z_854 : le (tf [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F] [([F, E, E, T, E, E, E, T, E, F, E, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F]), ([F, E, T, E, E, E, E, E, T, F, E, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_536 (And.intro z_853 trivial))

theorem z_855 : le (tf [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F] [([F, E, E, T, E, E, E, T, E, E, F, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F]), ([F, E, T, E, E, E, E, E, T, E, F, E, T, E, F], [F, E, T, E, E, E, E, E, T, E, F, E, T, F, E]), ([F, E, T, E, E, E, E, T, E, E, F, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_537 (And.intro z_846 (And.intro z_854 trivial)))

theorem z_856 : le (tf [E, F, T, E, E, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, T, E, E, F, T, E, E, F] [([E, F, E, T, E, E, E, T, E, E, F, T, E, E, F], [E, F, E, T, E, E, E, T, E, F, E, T, E, E, F]), ([E, F, T, E, E, E, E, E, T, E, F, T, E, E, F], [E, F, T, E, E, E, E, E, T, E, F, T, E, F, E]), ([E, F, T, E, E, E, E, T, E, E, F, E, T, E, F], [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_538 (And.intro z_847 (And.intro z_855 trivial)))

theorem z_857 : le (tf [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F] [([E, E, E, F, T, E, E, T, E, T, F, E, E, E, F], [E, E, F, E, T, E, E, T, E, T, F, E, E, E, F]), ([E, E, T, F, E, E, E, E, T, T, F, E, E, E, F], [E, E, T, F, E, E, E, E, T, T, F, E, E, F, E]), ([E, E, T, F, E, E, E, T, E, E, F, T, E, E, F], [E, F, T, E, E, E, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_802 (And.intro z_848 (And.intro z_856 trivial)))

theorem z_858 : le (tf [E, E, T, F, E, E, E, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, T, E, E, F, E, E, F] [([E, E, E, F, T, E, E, T, T, E, E, F, E, E, F], [E, E, F, E, T, E, E, T, T, E, E, F, E, E, F]), ([E, E, T, F, E, E, E, T, E, T, E, F, E, E, F], [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_797 (And.intro z_857 trivial))

theorem z_859 : le (tf [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F] [([F, E, E, E, E, T, T, E, E, E, F, E, E, T, F], [F, E, E, E, E, T, T, E, E, F, E, E, E, T, F]), ([F, E, E, E, T, E, E, T, E, E, F, E, E, T, F], [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 (And.intro z_784 trivial))

theorem z_860 : le (tf [F, E, E, E, T, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, E, E, E, E, F, T, E, F] [([F, E, E, E, E, T, T, E, E, E, E, F, T, E, F], [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F]), ([F, E, E, E, T, E, E, T, E, E, E, F, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F]), ([F, E, E, E, T, E, T, E, E, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_442 (And.intro z_785 (And.intro z_859 trivial)))

theorem z_861 : le (tf [E, F, E, E, T, E, T, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, E, E, T, F, E, E, F] [([E, F, E, E, E, T, T, E, E, E, T, F, E, E, F], [F, E, E, E, E, T, T, E, E, E, T, F, E, E, F]), ([E, F, E, E, T, E, E, T, E, E, T, F, E, E, F], [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F]), ([E, F, E, E, T, E, T, E, E, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_443 (And.intro z_786 (And.intro z_860 trivial)))

theorem z_862 : le (tf [E, E, F, E, T, E, T, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, E, T, E, F, E, E, F] [([E, E, F, E, E, T, T, E, E, T, E, F, E, E, F], [E, F, E, E, E, T, T, E, E, T, E, F, E, E, F]), ([E, E, F, E, T, E, E, T, E, T, E, F, E, E, F], [E, F, E, E, T, E, E, T, E, T, E, F, E, E, F]), ([E, E, F, E, T, E, T, E, E, E, T, F, E, E, F], [E, F, E, E, T, E, T, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 (And.intro z_796 (And.intro z_861 trivial)))

theorem z_863 : le (tf [E, F, E, E, T, E, T, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, E, F, E, T, E, E, F] [([E, F, E, E, E, T, T, E, E, F, E, T, E, E, F], [F, E, E, E, E, T, T, E, E, F, E, T, E, E, F]), ([E, F, E, E, T, E, E, T, E, F, E, T, E, E, F], [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F]), ([E, F, E, E, T, E, T, E, E, F, E, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_789 (And.intro z_498 (And.intro z_791 trivial)))

theorem z_864 : le (tf [E, E, F, E, T, E, T, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, E, F, T, E, E, E, F] [([E, E, F, E, E, T, T, E, E, F, T, E, E, E, F], [E, E, F, E, E, T, T, E, F, E, T, E, E, E, F]), ([E, E, F, E, T, E, E, T, E, F, T, E, E, E, F], [E, F, E, E, T, E, E, T, E, F, T, E, E, E, F]), ([E, E, F, E, T, E, T, E, E, F, E, T, E, E, F], [E, F, E, E, T, E, T, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_548 (And.intro z_499 (And.intro z_863 trivial)))

theorem z_865 : le (tf [E, F, E, E, T, E, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, T, T, E, E, E, F] [([E, F, E, E, E, T, E, E, F, T, T, E, E, E, F], [F, E, E, E, E, T, E, E, F, T, T, E, E, E, F]), ([E, F, E, E, T, E, E, E, F, T, E, T, E, E, F], [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_542 (And.intro z_798 trivial))

theorem z_866 : le (tf [E, F, E, E, T, E, E, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, F, E, E, T, E, E, F] [([E, F, E, E, E, T, E, T, F, E, E, T, E, E, F], [F, E, E, E, E, T, E, T, F, E, E, T, E, E, F]), ([E, F, E, E, T, E, E, E, F, T, E, T, E, E, F], [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F]), ([E, F, E, E, T, E, E, T, F, E, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_798 (And.intro z_497 trivial)))

theorem z_867 : le (tf [E, E, F, E, T, E, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, F, E, T, E, E, E, F] [([E, E, F, E, E, T, E, T, F, E, T, E, E, E, F], [E, F, E, E, E, T, E, T, F, E, T, E, E, E, F]), ([E, E, F, E, T, E, E, E, F, T, T, E, E, E, F], [E, F, E, E, T, E, E, E, F, T, T, E, E, E, F]), ([E, E, F, E, T, E, E, T, F, E, E, T, E, E, F], [E, F, E, E, T, E, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_543 (And.intro z_865 (And.intro z_866 trivial)))

theorem z_868 : le (tf [F, E, T, E, E, E, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, E, T, T, E, F, E] [([F, E, E, T, E, E, E, E, F, E, T, T, E, F, E], [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E]), ([F, E, T, E, E, E, E, E, F, E, T, E, T, F, E], [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_740 (And.intro z_834 trivial))

theorem z_869 : le (tf [F, E, T, E, E, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, T, E, T, E, E, F] [([F, E, E, T, E, E, E, E, F, T, E, T, E, E, F], [F, E, E, T, E, E, E, F, E, T, E, T, E, E, F]), ([F, E, T, E, E, E, E, E, F, E, T, T, E, E, F], [F, E, T, E, E, E, E, E, F, E, T, T, E, F, E]), ([F, E, T, E, E, E, E, E, F, T, E, E, T, E, F], [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_741 (And.intro z_868 (And.intro z_838 trivial)))

theorem z_870 : le (tf [E, F, T, E, E, E, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, F, T, T, E, E, E, F] [([E, F, E, T, E, E, E, E, F, T, T, E, E, E, F], [E, F, E, T, E, E, E, F, E, T, T, E, E, E, F]), ([E, F, T, E, E, E, E, E, F, T, E, T, E, E, F], [F, E, T, E, E, E, E, E, F, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_742 (And.intro z_869 trivial))

theorem z_871 : le (tf [E, F, E, E, E, T, F, T, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, E, E, T, E, E, F] [([E, F, E, E, E, T, F, E, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F]), ([E, F, E, E, E, T, F, T, E, E, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 (And.intro z_433 trivial))

theorem z_872 : le (tf [E, F, E, E, T, E, F, E, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, T, E, E, T, E, E, F] [([E, F, E, E, E, T, F, E, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F]), ([E, F, E, E, T, E, F, E, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F]), ([E, F, E, E, T, E, F, E, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 (And.intro z_479 (And.intro z_483 trivial)))

theorem z_873 : le (tf [E, F, E, E, T, E, F, T, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, E, E, E, T, E, F] [([E, F, E, E, E, T, F, T, E, E, E, E, T, E, F], [F, E, E, E, E, T, F, T, E, E, E, E, T, E, F]), ([E, F, E, E, T, E, F, E, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F]), ([E, F, E, E, T, E, F, T, E, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 (And.intro z_483 (And.intro z_496 trivial)))

theorem z_874 : le (tf [E, E, F, E, T, E, F, T, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, T, E, E, E, T, E, E, F] [([E, E, F, E, E, T, F, T, E, E, E, T, E, E, F], [E, F, E, E, E, T, F, T, E, E, E, T, E, E, F]), ([E, E, F, E, T, E, F, E, T, E, E, T, E, E, F], [E, F, E, E, T, E, F, E, T, E, E, T, E, E, F]), ([E, E, F, E, T, E, F, T, E, E, E, E, T, E, F], [E, F, E, E, T, E, F, T, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_871 (And.intro z_872 (And.intro z_873 trivial)))

theorem z_875 : le (tf [F, E, E, E, E, F, T, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, E, E, T, E, F] [([F, E, E, E, E, F, E, T, T, E, E, E, T, E, F], [F, E, E, E, F, E, E, T, T, E, E, E, T, E, F]), ([F, E, E, E, E, F, T, E, E, T, E, E, T, E, F], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]), ([F, E, E, E, E, F, T, E, T, E, E, E, E, T, F], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 (And.intro z_147 (And.intro z_348 trivial)))

theorem z_876 : le (tf [E, F, E, E, E, F, T, E, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, T, E, E, T, E, E, F] [([E, F, E, E, E, F, E, T, T, E, E, T, E, E, F], [F, E, E, E, E, F, E, T, T, E, E, T, E, E, F]), ([E, F, E, E, E, F, T, E, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F]), ([E, F, E, E, E, F, T, E, T, E, E, E, T, E, F], [F, E, E, E, E, F, T, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 (And.intro z_265 (And.intro z_875 trivial)))

theorem z_877 : le (tf [E, F, E, E, T, F, E, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, E, T, F, T, E, E] [([E, F, E, E, E, F, T, E, E, E, T, F, T, E, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]), ([E, F, E, E, T, F, E, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_143 (And.intro z_472 trivial))

theorem z_878 : le (tf [E, F, E, E, T, F, E, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, E, T, T, E, F, E] [([E, F, E, E, E, F, T, E, E, E, T, T, E, F, E], [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]), ([E, F, E, E, T, F, E, E, E, E, T, E, T, F, E], [E, F, E, E, T, F, E, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_264 (And.intro z_877 trivial))

theorem z_879 : le (tf [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E] [([E, F, E, E, E, F, T, E, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]), ([E, F, E, E, T, F, E, E, E, E, T, E, T, F, E], [E, F, E, E, T, F, E, E, E, E, T, F, T, E, E]), ([E, F, E, E, T, F, E, E, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 (And.intro z_877 (And.intro z_477 trivial)))

theorem z_880 : le (tf [E, F, E, E, T, F, E, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, T, E, T, E, E, F] [([E, F, E, E, E, F, T, E, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F]), ([E, F, E, E, T, F, E, E, E, E, T, T, E, E, F], [E, F, E, E, T, F, E, E, E, E, T, T, E, F, E]), ([E, F, E, E, T, F, E, E, E, T, E, E, T, E, F], [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_878 (And.intro z_879 trivial)))

theorem z_881 : le (tf [E, F, E, E, T, F, E, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, E, E, E, T, E, F] [([E, F, E, E, E, F, T, E, T, E, E, E, T, E, F], [F, E, E, E, E, F, T, E, T, E, E, E, T, E, F]), ([E, F, E, E, T, F, E, E, E, T, E, E, T, E, F], [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E]), ([E, F, E, E, T, F, E, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_875 (And.intro z_879 (And.intro z_482 trivial)))

theorem z_882 : le (tf [E, E, F, E, T, F, E, E, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, T, E, E, T, E, E, F] [([E, E, F, E, E, F, T, E, T, E, E, T, E, E, F], [E, F, E, E, E, F, T, E, T, E, E, T, E, E, F]), ([E, E, F, E, T, F, E, E, E, T, E, T, E, E, F], [E, F, E, E, T, F, E, E, E, T, E, T, E, E, F]), ([E, E, F, E, T, F, E, E, T, E, E, E, T, E, F], [E, F, E, E, T, F, E, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_876 (And.intro z_880 (And.intro z_881 trivial)))

theorem z_883 : le (tf [F, E, E, F, E, E, E, F, E, T, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, F, E, T, T, E, E, T, E] [([F, E, E, F, E, E, E, F, E, T, E, T, E, T, E], [F, E, F, E, E, E, E, F, E, T, E, T, E, T, E]), ([F, E, E, F, E, E, E, F, E, T, T, E, E, E, T], [F, E, F, E, E, E, E, F, E, T, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_375 (And.intro z_394 trivial))

theorem z_884 : le (tf [F, E, E, E, F, E, E, F, T, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, F, T, E, T, E, E, T, E] [([F, E, E, E, F, E, E, F, E, T, T, E, E, T, E], [F, E, E, F, E, E, E, F, E, T, T, E, E, T, E]), ([F, E, E, E, F, E, E, F, T, E, E, T, E, T, E], [F, E, E, F, E, E, E, F, T, E, E, T, E, T, E]), ([F, E, E, E, F, E, E, F, T, E, T, E, E, E, T], [F, E, E, F, E, E, E, F, T, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_883 (And.intro z_378 (And.intro z_395 trivial)))

theorem z_885 : le (tf [E, F, E, E, F, E, T, F, E, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, E, T, F, E, E, T, E, E, T, E] [([E, F, E, E, F, E, E, F, T, E, T, E, E, T, E], [F, E, E, E, F, E, E, F, T, E, T, E, E, T, E]), ([E, F, E, E, F, E, T, F, E, E, E, T, E, T, E], [F, E, E, E, F, E, T, F, E, E, E, T, E, T, E]), ([E, F, E, E, F, E, T, F, E, E, T, E, E, E, T], [F, E, E, E, F, E, T, F, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_884 (And.intro z_383 (And.intro z_396 trivial)))

theorem z_886 : le (tf [E, F, E, E, F, T, E, E, F, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, E, F, E, T, E, E, T, E] [([E, F, E, E, F, E, T, E, F, E, T, E, E, T, E], [E, F, E, E, F, E, T, F, E, E, T, E, E, T, E]), ([E, F, E, E, F, T, E, E, F, E, E, T, E, T, E], [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E]), ([E, F, E, E, F, T, E, E, F, E, T, E, E, E, T], [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_885 (And.intro z_388 (And.intro z_397 trivial)))

theorem z_887 : le (tf [F, E, F, E, E, T, E, F, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, T, E, F, E, E, E, E, E, T, T] [([F, E, F, E, E, E, T, F, E, E, E, E, E, T, T], [F, F, E, E, E, E, T, F, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_379 trivial)

theorem z_888 : le (tf [F, E, E, F, E, T, E, F, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, E, F, E, E, E, E, T, E, T] [([F, E, E, F, E, E, T, F, E, E, E, E, T, E, T], [F, E, F, E, E, E, T, F, E, E, E, E, T, E, T]), ([F, E, E, F, E, T, E, F, E, E, E, E, E, T, T], [F, E, F, E, E, T, E, F, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_380 (And.intro z_887 trivial))

theorem z_889 : le (tf [F, E, F, E, E, E, F, T, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, F, T, E, E, E, E, E, T, T] [([F, E, F, E, E, E, F, E, T, E, E, E, E, T, T], [F, F, E, E, E, E, F, E, T, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 trivial)

theorem z_890 : le (tf [F, E, E, F, E, T, F, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, T, F, E, E, E, E, E, E, T, T] [([F, E, E, F, E, E, F, T, E, E, E, E, E, T, T], [F, E, F, E, E, E, F, T, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_889 trivial)

theorem z_891 : le (tf [F, E, E, T, F, E, F, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, F, E, E, E, E, E, E, T, T] [([F, E, E, E, F, T, F, E, E, E, E, E, E, T, T], [F, E, E, F, E, T, F, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_890 trivial)

theorem z_892 : le (tf [F, E, E, T, F, E, E, F, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, F, E, E, E, E, T, E, T] [([F, E, E, E, F, T, E, F, E, E, E, E, T, E, T], [F, E, E, F, E, T, E, F, E, E, E, E, T, E, T]), ([F, E, E, T, F, E, E, F, E, E, E, E, E, T, T], [F, E, E, T, F, E, F, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_888 (And.intro z_891 trivial))

theorem z_893 : le (tf [F, E, E, T, F, E, E, E, F, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, F, E, E, E, T, T, E] [([F, E, E, E, F, T, E, E, F, E, E, E, T, T, E], [F, E, E, F, E, T, E, E, F, E, E, E, T, T, E]), ([F, E, E, T, F, E, E, E, F, E, E, E, T, E, T], [F, E, E, T, F, E, E, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_386 (And.intro z_892 trivial))

theorem z_894 : le (tf [F, E, E, T, F, E, E, E, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, F, E, E, T, E, E, T] [([F, E, E, E, F, T, E, E, F, E, E, T, E, E, T], [F, E, E, F, E, T, E, E, F, E, E, T, E, E, T]), ([F, E, E, T, F, E, E, E, F, E, E, E, T, E, T], [F, E, E, T, F, E, E, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 (And.intro z_892 trivial))

theorem z_895 : le (tf [F, E, E, T, F, E, E, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, F, E, T, E, T, E] [([F, E, E, E, F, T, E, E, E, F, E, T, E, T, E], [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E]), ([F, E, E, T, F, E, E, E, E, F, E, E, T, T, E], [F, E, E, T, F, E, E, E, F, E, E, E, T, T, E]), ([F, E, E, T, F, E, E, E, E, F, E, T, E, E, T], [F, E, E, T, F, E, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 (And.intro z_893 (And.intro z_894 trivial)))

theorem z_896 : le (tf [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T] [([F, E, E, E, F, T, E, E, E, F, T, E, E, E, T], [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T]), ([F, E, E, T, F, E, E, E, E, F, E, T, E, E, T], [F, E, E, T, F, E, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_397 (And.intro z_894 trivial))

theorem z_897 : le (tf [E, F, E, T, F, E, E, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, F, T, E, E, T, E] [([E, F, E, E, F, T, E, E, E, F, T, E, E, T, E], [E, F, E, E, F, T, E, E, F, E, T, E, E, T, E]), ([E, F, E, T, F, E, E, E, E, F, E, T, E, T, E], [F, E, E, T, F, E, E, E, E, F, E, T, E, T, E]), ([E, F, E, T, F, E, E, E, E, F, T, E, E, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_886 (And.intro z_895 (And.intro z_896 trivial)))

theorem z_898 : le (tf [F, E, E, T, F, E, E, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, F, E, T, T, E] [([F, E, E, E, F, T, E, E, E, E, F, E, T, T, E], [F, E, E, F, E, T, E, E, E, E, F, E, T, T, E]), ([F, E, E, T, F, E, E, E, E, E, F, E, T, E, T], [F, E, F, T, E, E, E, E, E, E, F, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_519 trivial))

theorem z_899 : le (tf [F, F, T, E, E, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, F, T, E, E, E, E, E, E, E, E, F, E, T, T] [([F, F, E, T, E, E, E, E, E, E, E, F, E, T, T], [F, F, E, T, E, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_518 trivial)

theorem z_900 : le (tf [F, E, T, F, E, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, E, E, F, T, E, T] [([F, E, E, F, T, E, E, E, E, E, E, F, T, E, T], [F, E, F, E, T, E, E, E, E, E, E, F, T, E, T]), ([F, E, T, F, E, E, E, E, E, E, E, F, E, T, T], [F, F, T, E, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_463 (And.intro z_899 trivial))

theorem z_901 : le (tf [F, E, T, E, F, E, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, E, F, T, T, E] [([F, E, E, T, F, E, E, E, E, E, E, F, T, T, E], [F, E, E, T, F, E, E, E, E, E, F, E, T, T, E]), ([F, E, T, E, F, E, E, E, E, E, E, F, T, E, T], [F, E, T, F, E, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_898 (And.intro z_900 trivial))

theorem z_902 : le (tf [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T] [([F, E, E, T, F, E, E, E, E, E, T, F, E, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T]), ([F, E, T, E, F, E, E, E, E, E, E, F, T, E, T], [F, E, T, F, E, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_896 (And.intro z_900 trivial))

theorem z_903 : le (tf [E, F, T, E, F, E, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, F, E, E, E, E, E, T, F, E, T, E] [([E, F, E, T, F, E, E, E, E, E, T, F, E, T, E], [E, F, E, T, F, E, E, E, E, F, T, E, E, T, E]), ([E, F, T, E, F, E, E, E, E, E, E, F, T, T, E], [F, E, T, E, F, E, E, E, E, E, E, F, T, T, E]), ([E, F, T, E, F, E, E, E, E, E, T, F, E, E, T], [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_897 (And.intro z_901 (And.intro z_902 trivial)))

theorem z_904 : le (tf [E, E, T, F, F, E, E, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, E, E, T, F, T, E, E] [([E, E, T, F, F, E, E, E, E, E, T, F, E, T, E], [E, F, T, E, F, E, E, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_903 trivial)

theorem z_905 : le (tf [E, E, T, F, F, E, E, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, E, E, T, T, E, F, E] [([E, E, T, F, F, E, E, E, E, E, T, E, T, F, E], [E, E, T, F, F, E, E, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_904 trivial)

theorem z_906 : le (tf [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T] [([F, E, E, E, F, T, E, E, E, E, T, E, F, E, T], [F, E, E, E, F, T, E, E, E, E, T, F, E, E, T]), ([F, E, E, T, F, E, E, E, E, E, E, T, F, E, T], [F, E, E, T, F, E, E, E, E, E, F, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_218 (And.intro z_520 trivial))

theorem z_907 : le (tf [F, E, E, T, F, E, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, T, E, E, E, F, T] [([F, E, E, E, F, T, E, E, E, T, E, E, E, F, T], [F, E, E, F, E, T, E, E, E, T, E, E, E, F, T]), ([F, E, E, T, F, E, E, E, E, E, T, E, E, F, T], [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_417 (And.intro z_906 trivial))

theorem z_908 : le (tf [F, E, T, E, F, E, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, E, T, E, E, F, T] [([F, E, E, T, F, E, E, E, E, E, T, E, E, F, T], [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T]), ([F, E, T, E, F, E, E, E, E, E, E, T, E, F, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_906 (And.intro z_849 trivial))

theorem z_909 : le (tf [E, F, T, E, F, E, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, F, E, E, E, E, T, E, E, E, F, T] [([E, F, E, T, F, E, E, E, E, T, E, E, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, E, E, F, T]), ([E, F, T, E, F, E, E, E, E, E, T, E, E, F, T], [F, E, T, E, F, E, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_907 (And.intro z_908 trivial))

theorem z_910 : le (tf [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E] [([E, E, T, F, F, E, E, E, E, E, T, E, T, F, E], [E, E, T, F, F, E, E, E, E, E, T, F, T, E, E]), ([E, E, T, F, F, E, E, E, E, T, E, E, E, F, T], [E, F, T, E, F, E, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_904 (And.intro z_909 trivial))

theorem z_911 : le (tf [E, E, T, F, F, E, E, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, E, T, E, T, E, E, F] [([E, E, T, F, F, E, E, E, E, E, T, T, E, E, F], [E, E, T, F, F, E, E, E, E, E, T, T, E, F, E]), ([E, E, T, F, F, E, E, E, E, T, E, E, T, E, F], [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_905 (And.intro z_910 trivial))

theorem z_912 : le (tf [F, E, E, F, E, E, E, T, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, T, T, E, E, F, E, T, E] [([F, E, E, F, E, E, E, T, E, T, E, F, E, T, E], [F, E, E, F, E, E, E, T, E, T, F, E, E, T, E]), ([F, E, E, F, E, E, E, T, T, E, E, F, E, E, T], [F, E, F, E, E, E, E, T, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_426 trivial))

theorem z_913 : le (tf [F, E, E, E, F, E, T, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, E, T, E, E, F, E, T, E] [([F, E, E, E, F, E, E, T, T, E, E, F, E, T, E], [F, E, E, F, E, E, E, T, T, E, E, F, E, T, E]), ([F, E, E, E, F, E, T, E, E, T, E, F, E, T, E], [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E]), ([F, E, E, E, F, E, T, E, T, E, E, F, E, E, T], [F, E, E, F, E, E, T, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_912 (And.intro z_341 (And.intro z_427 trivial)))

theorem z_914 : le (tf [E, F, E, E, F, T, E, E, E, T, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, E, E, T, F, E, E, T, E] [([E, F, E, E, F, E, T, E, E, T, F, E, E, T, E], [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E]), ([E, F, E, E, F, T, E, E, E, E, F, T, E, T, E], [F, E, E, E, F, T, E, E, E, E, F, T, E, T, E]), ([E, F, E, E, F, T, E, E, E, T, F, E, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_341 (And.intro z_405 (And.intro z_406 trivial)))

theorem z_915 : le (tf [E, F, E, E, F, T, E, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, E, T, E, E, F, E, T, E] [([E, F, E, E, F, E, T, E, T, E, E, F, E, T, E], [F, E, E, E, F, E, T, E, T, E, E, F, E, T, E]), ([E, F, E, E, F, T, E, E, E, T, E, F, E, T, E], [E, F, E, E, F, T, E, E, E, T, F, E, E, T, E]), ([E, F, E, E, F, T, E, E, T, E, E, F, E, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_913 (And.intro z_914 (And.intro z_428 trivial)))

theorem z_916 : le (tf [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T] [([F, E, E, E, F, T, E, E, E, T, E, F, E, E, T], [F, E, E, E, F, T, E, E, E, T, F, E, E, E, T]), ([F, E, E, T, F, E, E, E, E, E, T, F, E, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_406 (And.intro z_896 trivial))

theorem z_917 : le (tf [E, F, E, T, F, E, E, E, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, T, E, F, E, T, E] [([E, F, E, E, F, T, E, E, E, T, E, F, E, T, E], [E, F, E, E, F, T, E, E, E, T, F, E, E, T, E]), ([E, F, E, T, F, E, E, E, E, E, T, F, E, T, E], [E, F, E, T, F, E, E, E, E, F, T, E, E, T, E]), ([E, F, E, T, F, E, E, E, E, T, E, F, E, E, T], [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_914 (And.intro z_897 (And.intro z_916 trivial)))

theorem z_918 : le (tf [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T] [([F, E, E, E, F, T, E, E, T, E, E, E, F, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T]), ([F, E, E, T, F, E, E, E, E, T, E, E, F, E, T], [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_428 (And.intro z_916 trivial))

theorem z_919 : le (tf [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E] [([E, F, E, E, F, T, E, E, T, E, E, E, F, T, E], [E, F, E, E, F, T, E, E, T, E, E, F, E, T, E]), ([E, F, E, T, F, E, E, E, E, T, E, E, F, T, E], [E, F, E, T, F, E, E, E, E, T, E, F, E, T, E]), ([E, F, E, T, F, E, E, E, T, E, E, E, F, E, T], [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_915 (And.intro z_917 (And.intro z_918 trivial)))

theorem z_920 : le (tf [F, E, T, E, F, E, E, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, T, E, E, F, E, T] [([F, E, E, T, F, E, E, E, E, T, E, E, F, E, T], [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T]), ([F, E, T, E, F, E, E, E, E, E, T, E, F, E, T], [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_916 (And.intro z_902 trivial))

theorem z_921 : le (tf [E, F, T, E, F, E, E, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, F, E, E, E, E, T, E, E, F, T, E] [([E, F, E, T, F, E, E, E, E, T, E, E, F, T, E], [E, F, E, T, F, E, E, E, E, T, E, F, E, T, E]), ([E, F, T, E, F, E, E, E, E, E, T, E, F, T, E], [E, F, T, E, F, E, E, E, E, E, T, F, E, T, E]), ([E, F, T, E, F, E, E, E, E, T, E, E, F, E, T], [F, E, T, E, F, E, E, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_917 (And.intro z_903 (And.intro z_920 trivial)))

theorem z_922 : le (tf [E, F, T, E, F, E, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, F, E, E, E, T, E, E, E, E, T, F] [([E, F, E, T, F, E, E, E, T, E, E, E, E, T, F], [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E]), ([E, F, T, E, F, E, E, E, E, T, E, E, E, T, F], [E, F, T, E, F, E, E, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_919 (And.intro z_921 trivial))

theorem z_923 : le (tf [E, E, T, F, F, E, E, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, T, E, E, E, T, E, F] [([E, E, T, F, F, E, E, E, E, T, E, E, T, E, F], [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E]), ([E, E, T, F, F, E, E, E, T, E, E, E, E, T, F], [E, F, T, E, F, E, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_910 (And.intro z_922 trivial))

theorem z_924 : le (tf [E, E, T, F, E, F, E, E, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, T, E, E, T, E, E, F] [([E, E, E, F, T, F, E, E, T, E, E, T, E, E, F], [E, E, F, E, T, F, E, E, T, E, E, T, E, E, F]), ([E, E, T, F, E, F, E, E, E, T, E, T, E, E, F], [E, E, T, F, F, E, E, E, E, T, E, T, E, E, F]), ([E, E, T, F, E, F, E, E, T, E, E, E, T, E, F], [E, E, T, F, F, E, E, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_882 (And.intro z_911 (And.intro z_923 trivial)))

theorem z_925 : le (tf [F, E, E, E, E, F, T, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, E, E, E, E, T, F] [([F, E, E, E, E, F, T, E, T, E, E, E, E, T, F], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 trivial)

theorem z_926 : le (tf [E, F, E, E, E, F, T, T, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, T, E, E, E, E, T, E, F] [([E, F, E, E, E, F, T, E, T, E, E, E, T, E, F], [F, E, E, E, E, F, T, E, T, E, E, E, T, E, F]), ([E, F, E, E, E, F, T, T, E, E, E, E, E, T, F], [F, E, E, E, E, F, T, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_875 (And.intro z_925 trivial))

theorem z_927 : le (tf [E, F, E, E, T, F, E, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, E, E, E, E, T, F] [([E, F, E, E, E, F, T, T, E, E, E, E, E, T, F], [F, E, E, E, E, F, T, T, E, E, E, E, E, T, F]), ([E, F, E, E, T, F, E, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_925 (And.intro z_482 trivial))

theorem z_928 : le (tf [E, E, F, E, T, F, E, T, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, T, E, E, E, E, T, E, F] [([E, E, F, E, E, F, T, T, E, E, E, E, T, E, F], [E, F, E, E, E, F, T, T, E, E, E, E, T, E, F]), ([E, E, F, E, T, F, E, E, T, E, E, E, T, E, F], [E, F, E, E, T, F, E, E, T, E, E, E, T, E, F]), ([E, E, F, E, T, F, E, T, E, E, E, E, E, T, F], [E, F, E, E, T, F, E, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_926 (And.intro z_881 (And.intro z_927 trivial)))

theorem z_929 : le (tf [F, E, E, E, F, E, T, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, T, T, E, E, E, E, F, T, E] [([F, E, E, E, F, E, T, E, T, E, E, E, F, T, E], [F, E, E, E, F, E, T, E, T, E, E, F, E, T, E]), ([F, E, E, E, F, E, T, T, E, E, E, E, F, E, T], [F, E, E, F, E, E, T, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_913 (And.intro z_430 trivial))

theorem z_930 : le (tf [E, F, E, E, F, T, E, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, T, E, E, E, E, F, T, E] [([E, F, E, E, F, E, T, T, E, E, E, E, F, T, E], [F, E, E, E, F, E, T, T, E, E, E, E, F, T, E]), ([E, F, E, E, F, T, E, E, T, E, E, E, F, T, E], [E, F, E, E, F, T, E, E, T, E, E, F, E, T, E]), ([E, F, E, E, F, T, E, T, E, E, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_929 (And.intro z_915 (And.intro z_431 trivial)))

theorem z_931 : le (tf [E, F, E, T, F, E, E, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, T, E, E, E, E, E, T, F] [([E, F, E, E, F, T, E, T, E, E, E, E, E, T, F], [E, F, E, E, F, T, E, T, E, E, E, E, F, T, E]), ([E, F, E, T, F, E, E, E, T, E, E, E, E, T, F], [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 (And.intro z_919 trivial))

theorem z_932 : le (tf [E, F, T, E, E, F, E, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, T, E, E, E, E, E, T, F] [([E, F, E, T, E, F, E, T, E, E, E, E, E, T, F], [E, F, E, T, F, E, E, T, E, E, E, E, E, T, F]), ([E, F, T, E, E, F, E, E, T, E, E, E, E, T, F], [E, F, T, E, F, E, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_931 (And.intro z_922 trivial))

theorem z_933 : le (tf [E, E, T, F, E, F, E, T, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, T, E, E, E, E, T, E, F] [([E, E, E, F, T, F, E, T, E, E, E, E, T, E, F], [E, E, F, E, T, F, E, T, E, E, E, E, T, E, F]), ([E, E, T, F, E, F, E, E, T, E, E, E, T, E, F], [E, E, T, F, F, E, E, E, T, E, E, E, T, E, F]), ([E, E, T, F, E, F, E, T, E, E, E, E, E, T, F], [E, F, T, E, E, F, E, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_928 (And.intro z_923 (And.intro z_932 trivial)))

theorem z_934 : le (tf [E, E, T, F, E, E, F, T, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, E, E, E, T, E, E, F] [([E, E, E, F, T, E, F, T, E, E, E, T, E, E, F], [E, E, F, E, T, E, F, T, E, E, E, T, E, E, F]), ([E, E, T, F, E, E, F, E, T, E, E, T, E, E, F], [E, E, T, F, E, F, E, E, T, E, E, T, E, E, F]), ([E, E, T, F, E, E, F, T, E, E, E, E, T, E, F], [E, E, T, F, E, F, E, T, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_874 (And.intro z_924 (And.intro z_933 trivial)))

theorem z_935 : le (tf [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F] [([E, E, E, F, T, E, E, T, F, E, T, E, E, E, F], [E, E, F, E, T, E, E, T, F, E, T, E, E, E, F]), ([E, E, T, F, E, E, E, E, F, T, T, E, E, E, F], [E, F, T, E, E, E, E, E, F, T, T, E, E, E, F]), ([E, E, T, F, E, E, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, E, F, T, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_867 (And.intro z_870 (And.intro z_934 trivial)))

theorem z_936 : le (tf [E, F, E, E, T, E, T, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, F, E, E, E, T, E, F] [([E, F, E, E, E, T, T, E, F, E, E, E, T, E, F], [F, E, E, E, E, T, T, E, F, E, E, E, T, E, F]), ([E, F, E, E, T, E, E, T, F, E, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F]), ([E, F, E, E, T, E, T, E, F, E, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_546 (And.intro z_497 (And.intro z_790 trivial)))

theorem z_937 : le (tf [E, E, F, E, T, E, T, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, F, E, E, T, E, E, F] [([E, E, F, E, E, T, T, E, F, E, E, T, E, E, F], [E, F, E, E, E, T, T, E, F, E, E, T, E, E, F]), ([E, E, F, E, T, E, E, T, F, E, E, T, E, E, F], [E, F, E, E, T, E, E, T, F, E, E, T, E, E, F]), ([E, E, F, E, T, E, T, E, F, E, E, E, T, E, F], [E, F, E, E, T, E, T, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_547 (And.intro z_866 (And.intro z_936 trivial)))

theorem z_938 : le (tf [F, E, E, E, E, F, E, T, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, E, T, E, T, F, E] [([F, E, E, E, E, F, E, E, T, E, T, E, T, F, E], [F, E, E, E, F, E, E, E, T, E, T, E, T, F, E]), ([F, E, E, E, E, F, E, T, E, E, E, T, T, F, E], [F, E, E, E, F, E, E, T, E, E, E, T, T, F, E]), ([F, E, E, E, E, F, E, T, E, E, T, E, E, F, T], [F, E, E, E, E, F, E, T, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 (And.intro z_68 (And.intro z_27 trivial)))

theorem z_939 : le (tf [F, E, E, E, E, E, F, T, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, T, E, E, T, F, E] [([F, E, E, E, E, E, F, E, T, T, E, E, T, F, E], [F, E, E, E, E, F, E, E, T, T, E, E, T, F, E]), ([F, E, E, E, E, E, F, T, E, E, T, E, T, F, E], [F, E, E, E, E, F, E, T, E, E, T, E, T, F, E]), ([F, E, E, E, E, E, F, T, E, T, E, E, E, F, T], [F, E, E, E, E, F, E, T, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_271 (And.intro z_938 (And.intro z_221 trivial)))

theorem z_940 : le (tf [E, F, E, E, E, T, F, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, E, T, F, T, E, E] [([E, F, E, E, E, E, F, T, E, E, T, F, T, E, E], [E, F, E, E, E, E, F, T, E, F, T, E, T, E, E]), ([E, F, E, E, E, T, F, E, E, E, T, F, E, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_677 (And.intro z_219 trivial))

theorem z_941 : le (tf [E, F, E, E, E, T, F, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, T, E, E, T, F, E] [([E, F, E, E, E, E, F, T, E, T, E, E, T, F, E], [F, E, E, E, E, E, F, T, E, T, E, E, T, F, E]), ([E, F, E, E, E, T, F, E, E, E, T, E, T, F, E], [E, F, E, E, E, T, F, E, E, E, T, F, T, E, E]), ([E, F, E, E, E, T, F, E, E, T, E, E, E, F, T], [F, E, E, E, E, T, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_939 (And.intro z_940 (And.intro z_223 trivial)))

theorem z_942 : le (tf [F, E, E, E, E, F, T, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, T, E, T, E, F] [([F, E, E, E, E, F, E, T, E, E, T, E, T, E, F], [F, E, E, E, E, F, E, T, E, E, T, E, T, F, E]), ([F, E, E, E, E, F, T, E, E, E, E, T, T, E, F], [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]), ([F, E, E, E, E, F, T, E, E, E, T, E, E, T, F], [F, E, E, E, F, E, T, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_938 (And.intro z_82 (And.intro z_168 trivial)))

theorem z_943 : le (tf [F, E, E, E, T, F, E, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, E, T, T, E, F] [([F, E, E, E, E, F, T, E, E, E, E, T, T, E, F], [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]), ([F, E, E, E, T, F, E, E, E, E, E, T, E, T, F], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_529 trivial))

theorem z_944 : le (tf [E, F, E, E, T, F, E, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, E, T, E, T, E, F] [([E, F, E, E, E, F, T, E, E, E, T, E, T, E, F], [F, E, E, E, E, F, T, E, E, E, T, E, T, E, F]), ([E, F, E, E, T, F, E, E, E, E, E, T, T, E, F], [F, E, E, E, T, F, E, E, E, E, E, T, T, E, F]), ([E, F, E, E, T, F, E, E, E, E, T, E, E, T, F], [F, E, E, E, T, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_942 (And.intro z_943 (And.intro z_530 trivial)))

theorem z_945 : le (tf [E, F, E, E, T, E, F, E, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, T, E, E, T, E, F] [([E, F, E, E, E, T, F, E, E, T, E, E, T, E, F], [E, F, E, E, E, T, F, E, E, T, E, E, T, F, E]), ([E, F, E, E, T, E, F, E, E, E, T, E, T, E, F], [E, F, E, E, T, F, E, E, E, E, T, E, T, E, F]), ([E, F, E, E, T, E, F, E, E, T, E, E, E, T, F], [F, E, E, E, T, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_941 (And.intro z_944 (And.intro z_531 trivial)))

theorem z_946 : le (tf [E, F, E, E, T, E, E, F, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, E, E, T, E, F] [([E, F, E, E, E, T, E, F, T, E, E, E, T, E, F], [F, E, E, E, E, T, E, F, T, E, E, E, T, E, F]), ([E, F, E, E, T, E, E, F, E, T, E, E, T, E, F], [E, F, E, E, T, E, F, E, E, T, E, E, T, E, F]), ([E, F, E, E, T, E, E, F, T, E, E, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_945 (And.intro z_782 trivial)))

theorem z_947 : le (tf [E, F, E, E, T, E, T, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, E, E, T, F] [([E, F, E, E, E, T, T, F, E, E, E, E, E, T, F], [F, E, E, E, E, T, T, F, E, E, E, E, E, T, F]), ([E, F, E, E, T, E, E, F, T, E, E, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_545 (And.intro z_782 trivial))

theorem z_948 : le (tf [E, E, F, E, T, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, E, E, T, E, F] [([E, E, F, E, E, T, T, F, E, E, E, E, T, E, F], [E, F, E, E, E, T, T, F, E, E, E, E, T, E, F]), ([E, E, F, E, T, E, E, F, T, E, E, E, T, E, F], [E, F, E, E, T, E, E, F, T, E, E, E, T, E, F]), ([E, E, F, E, T, E, T, F, E, E, E, E, E, T, F], [E, F, E, E, T, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_735 (And.intro z_946 (And.intro z_947 trivial)))

theorem z_949 : le (tf [E, F, T, E, E, E, E, F, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, E, E, T, F, T, E, E] [([E, F, E, T, E, E, E, F, E, E, T, F, T, E, E], [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E]), ([E, F, T, E, E, E, E, F, E, E, T, F, E, T, E], [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_513 (And.intro z_833 trivial))

theorem z_950 : le (tf [E, F, T, E, E, E, E, F, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, E, T, E, E, T, F, E] [([E, F, E, T, E, E, E, F, E, T, E, E, T, F, E], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E]), ([E, F, T, E, E, E, E, F, E, E, T, E, T, F, E], [E, F, T, E, E, E, E, F, E, E, T, F, T, E, E]), ([E, F, T, E, E, E, E, F, E, T, E, E, E, F, T], [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_517 (And.intro z_949 (And.intro z_837 trivial)))

theorem z_951 : le (tf [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F] [([E, F, E, T, E, E, E, F, T, E, E, E, T, E, F], [F, E, E, T, E, E, E, F, T, E, E, E, T, E, F]), ([E, F, T, E, E, E, E, F, E, T, E, E, T, E, F], [E, F, T, E, E, E, E, F, E, T, E, E, T, F, E]), ([E, F, T, E, E, E, E, F, T, E, E, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_525 (And.intro z_950 (And.intro z_853 trivial)))

theorem z_952 : le (tf [E, F, T, E, E, E, T, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, F, E, E, E, E, E, T, F] [([E, F, E, T, E, E, T, F, E, E, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F]), ([E, F, T, E, E, E, E, F, T, E, E, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_759 (And.intro z_853 trivial))

theorem z_953 : le (tf [E, E, T, F, E, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, E, E, T, E, F] [([E, E, E, F, T, E, T, F, E, E, E, E, T, E, F], [E, E, F, E, T, E, T, F, E, E, E, E, T, E, F]), ([E, E, T, F, E, E, E, F, T, E, E, E, T, E, F], [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F]), ([E, E, T, F, E, E, T, F, E, E, E, E, E, T, F], [E, F, T, E, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_948 (And.intro z_951 (And.intro z_952 trivial)))

theorem z_954 : le (tf [E, E, T, F, E, E, T, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, F, E, E, T, E, E, F] [([E, E, E, F, T, E, T, E, F, E, E, T, E, E, F], [E, E, F, E, T, E, T, E, F, E, E, T, E, E, F]), ([E, E, T, F, E, E, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, E, F, T, E, E, E, T, E, E, F]), ([E, E, T, F, E, E, T, E, F, E, E, E, T, E, F], [E, E, T, F, E, E, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_937 (And.intro z_934 (And.intro z_953 trivial)))

theorem z_955 : le (tf [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F] [([E, E, E, F, T, E, T, E, E, F, T, E, E, E, F], [E, E, F, E, T, E, T, E, E, F, T, E, E, E, F]), ([E, E, T, F, E, E, E, T, E, F, T, E, E, E, F], [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F]), ([E, E, T, F, E, E, T, E, E, F, E, T, E, E, F], [E, E, T, F, E, E, T, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_864 (And.intro z_935 (And.intro z_954 trivial)))

theorem z_956 : le (tf [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F] [([E, E, E, F, T, E, T, E, E, T, E, F, E, E, F], [E, E, F, E, T, E, T, E, E, T, E, F, E, E, F]), ([E, E, T, F, E, E, E, T, E, T, E, F, E, E, F], [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F]), ([E, E, T, F, E, E, T, E, E, E, T, F, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_862 (And.intro z_857 (And.intro z_955 trivial)))

theorem z_957 : le (tf [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F] [([E, E, E, F, T, E, T, E, T, E, E, E, F, E, F], [E, E, F, E, T, E, T, E, T, E, E, E, F, E, F]), ([E, E, T, F, E, E, E, T, T, E, E, E, F, E, F], [E, E, T, F, E, E, E, T, T, E, E, F, E, E, F]), ([E, E, T, F, E, E, T, E, E, T, E, E, F, E, F], [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_795 (And.intro z_858 (And.intro z_956 trivial)))

theorem z_958 : le (tf [E, E, T, E, F, E, T, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, T, E, E, E, E, F, E, F] [([E, E, E, T, F, E, T, T, E, E, E, E, F, E, F], [E, E, E, T, F, E, T, T, E, E, E, F, E, E, F]), ([E, E, T, E, F, E, T, E, T, E, E, E, F, E, F], [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_765 (And.intro z_957 trivial))

theorem z_959 : le (tf [E, E, T, E, F, E, T, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, E, T, E, E, F, E, E, F] [([E, E, E, T, F, E, T, E, T, E, E, F, E, E, F], [E, E, E, T, F, E, T, E, T, E, F, E, E, E, F]), ([E, E, T, E, F, E, E, T, T, E, E, F, E, E, F], [E, E, T, F, E, E, E, T, T, E, E, F, E, E, F]), ([E, E, T, E, F, E, T, E, E, T, E, F, E, E, F], [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_764 (And.intro z_858 (And.intro z_956 trivial)))

theorem z_960 : le (tf [E, F, E, E, T, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, E, E, F, E, T, E, F] [([E, F, E, E, E, T, T, E, E, E, F, E, T, E, F], [F, E, E, E, E, T, T, E, E, E, F, E, T, E, F]), ([E, F, E, E, T, E, E, T, E, E, F, E, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F]), ([E, F, E, E, T, E, T, E, E, E, F, E, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_442 (And.intro z_785 (And.intro z_859 trivial)))

theorem z_961 : le (tf [E, E, F, E, T, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, E, E, E, F, T, E, E, F] [([E, E, F, E, E, T, T, E, E, E, F, T, E, E, F], [E, F, E, E, E, T, T, E, E, E, F, T, E, E, F]), ([E, E, F, E, T, E, E, T, E, E, F, T, E, E, F], [E, F, E, E, T, E, E, T, E, E, F, T, E, E, F]), ([E, E, F, E, T, E, T, E, E, E, F, E, T, E, F], [E, F, E, E, T, E, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_451 (And.intro z_801 (And.intro z_960 trivial)))

theorem z_962 : le (tf [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F] [([F, E, E, E, T, E, T, E, E, F, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F]), ([F, E, E, T, E, E, E, T, E, F, E, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_790 (And.intro z_536 trivial))

theorem z_963 : le (tf [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F] [([F, E, E, E, T, E, T, E, E, E, F, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F]), ([F, E, E, T, E, E, E, T, E, E, F, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F]), ([F, E, E, T, E, E, T, E, E, E, F, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_537 (And.intro z_962 trivial)))

theorem z_964 : le (tf [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F] [([F, E, E, T, E, E, T, E, E, E, F, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F]), ([F, E, T, E, E, E, E, T, E, E, F, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_962 (And.intro z_854 trivial))

theorem z_965 : le (tf [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F] [([E, F, E, T, E, E, T, E, E, E, F, E, T, E, F], [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F]), ([E, F, T, E, E, E, E, T, E, E, F, E, T, E, F], [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F]), ([E, F, T, E, E, E, T, E, E, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_963 (And.intro z_855 (And.intro z_964 trivial)))

theorem z_966 : le (tf [E, E, T, F, E, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, E, E, E, F, T, E, E, F] [([E, E, E, F, T, E, T, E, E, E, F, T, E, E, F], [E, E, F, E, T, E, T, E, E, E, F, T, E, E, F]), ([E, E, T, F, E, E, E, T, E, E, F, T, E, E, F], [E, F, T, E, E, E, E, T, E, E, F, T, E, E, F]), ([E, E, T, F, E, E, T, E, E, E, F, E, T, E, F], [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_961 (And.intro z_856 (And.intro z_965 trivial)))

theorem z_967 : le (tf [E, E, T, E, F, E, T, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, E, E, T, F, E, E, E, F] [([E, E, E, T, F, E, T, E, E, T, F, E, E, E, F], [E, E, E, T, F, E, T, E, F, T, E, E, E, E, F]), ([E, E, T, E, F, E, E, T, E, T, F, E, E, E, F], [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F]), ([E, E, T, E, F, E, T, E, E, E, F, T, E, E, F], [E, E, T, F, E, E, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_763 (And.intro z_857 (And.intro z_966 trivial)))

theorem z_968 : le (tf [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F] [([F, E, E, E, T, E, T, E, E, F, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_790 trivial)

theorem z_969 : le (tf [E, F, E, E, T, T, E, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, F, E, E, T, E, F] [([E, F, E, E, T, E, T, E, E, F, E, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F]), ([E, F, E, E, T, T, E, E, E, F, E, E, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_968 trivial))

theorem z_970 : le (tf [E, E, F, E, T, T, E, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, E, F, E, T, E, E, F] [([E, E, F, E, T, E, T, E, E, F, E, T, E, E, F], [E, F, E, E, T, E, T, E, E, F, E, T, E, E, F]), ([E, E, F, E, T, T, E, E, E, F, E, E, T, E, F], [E, F, E, E, T, T, E, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_863 (And.intro z_969 trivial))

theorem z_971 : le (tf [E, F, E, E, T, T, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, E, E, E, E, T, F] [([E, F, E, E, T, E, T, E, F, E, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_790 trivial)

theorem z_972 : le (tf [E, E, F, E, T, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, F, E, E, E, T, E, F] [([E, E, F, E, T, E, T, E, F, E, E, E, T, E, F], [E, F, E, E, T, E, T, E, F, E, E, E, T, E, F]), ([E, E, F, E, T, T, E, E, F, E, E, E, E, T, F], [E, F, E, E, T, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_936 (And.intro z_971 trivial))

theorem z_973 : le (tf [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F] [([F, E, E, E, T, E, T, F, E, E, E, E, E, T, F], [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_756 trivial)

theorem z_974 : le (tf [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F] [([F, E, E, E, T, T, E, E, F, E, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F]), ([F, E, E, T, E, E, T, E, F, E, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_973 (And.intro z_759 trivial))

theorem z_975 : le (tf [E, F, T, E, E, T, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, F, E, E, E, E, T, F] [([E, F, E, T, E, T, E, E, F, E, E, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F]), ([E, F, T, E, E, E, T, E, F, E, E, E, E, T, F], [E, F, T, E, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_974 (And.intro z_952 trivial))

theorem z_976 : le (tf [E, E, T, F, E, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, F, E, E, E, T, E, F] [([E, E, E, F, T, T, E, E, F, E, E, E, T, E, F], [E, E, F, E, T, T, E, E, F, E, E, E, T, E, F]), ([E, E, T, F, E, E, T, E, F, E, E, E, T, E, F], [E, E, T, F, E, E, T, F, E, E, E, E, T, E, F]), ([E, E, T, F, E, T, E, E, F, E, E, E, E, T, F], [E, F, T, E, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_972 (And.intro z_953 (And.intro z_975 trivial)))

theorem z_977 : le (tf [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F] [([E, E, E, F, T, T, E, E, E, F, E, T, E, E, F], [E, E, F, E, T, T, E, E, E, F, E, T, E, E, F]), ([E, E, T, F, E, E, T, E, E, F, E, T, E, E, F], [E, E, T, F, E, E, T, E, F, E, E, T, E, E, F]), ([E, E, T, F, E, T, E, E, E, F, E, E, T, E, F], [E, E, T, F, E, T, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_970 (And.intro z_954 (And.intro z_976 trivial)))

theorem z_978 : le (tf [F, E, E, T, T, E, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, E, E, F, E, E, E, T, F] [([F, E, E, T, E, T, E, E, E, F, E, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_974 trivial)

theorem z_979 : le (tf [E, F, T, E, T, E, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, T, E, E, E, E, F, E, E, E, T, F] [([E, F, E, T, T, E, E, E, E, F, E, E, E, T, F], [F, E, E, T, T, E, E, E, E, F, E, E, E, T, F]), ([E, F, T, E, E, T, E, E, E, F, E, E, E, T, F], [E, F, T, E, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_978 (And.intro z_975 trivial))

theorem z_980 : le (tf [E, E, T, F, T, E, E, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, E, E, F, E, E, T, E, F] [([E, E, T, F, E, T, E, E, E, F, E, E, T, E, F], [E, E, T, F, E, T, E, E, F, E, E, E, T, E, F]), ([E, E, T, F, T, E, E, E, E, F, E, E, E, T, F], [E, F, T, E, T, E, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_976 (And.intro z_979 trivial))

theorem z_981 : le (tf [E, E, T, F, T, E, E, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, E, E, E, F, T, E, E, F] [([E, E, T, F, E, T, E, E, E, E, F, T, E, E, F], [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F]), ([E, E, T, F, T, E, E, E, E, E, F, E, T, E, F], [E, E, T, F, T, E, E, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_977 (And.intro z_980 trivial))

theorem z_982 : le (tf [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F] [([E, E, E, T, T, F, E, E, E, T, F, E, E, E, F], [E, E, E, T, T, F, E, E, F, T, E, E, E, E, F]), ([E, E, T, E, E, F, T, E, E, T, F, E, E, E, F], [E, E, T, E, F, E, T, E, E, T, F, E, E, E, F]), ([E, E, T, E, T, F, E, E, E, E, F, T, E, E, F], [E, E, T, F, T, E, E, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_770 (And.intro z_967 (And.intro z_981 trivial)))

theorem z_983 : le (tf [E, E, T, E, T, F, E, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, E, T, E, E, F, E, E, F] [([E, E, E, T, T, F, E, E, T, E, E, F, E, E, F], [E, E, E, T, T, F, E, E, T, E, F, E, E, E, F]), ([E, E, T, E, E, F, T, E, T, E, E, F, E, E, F], [E, E, T, E, F, E, T, E, T, E, E, F, E, E, F]), ([E, E, T, E, T, F, E, E, E, T, E, F, E, E, F], [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_771 (And.intro z_959 (And.intro z_982 trivial)))

theorem z_984 : le (tf [E, E, T, E, T, F, E, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, T, E, E, E, E, F, E, F] [([E, E, E, T, T, F, E, T, E, E, E, E, F, E, F], [E, E, E, T, T, F, E, T, E, E, E, F, E, E, F]), ([E, E, T, E, E, F, T, T, E, E, E, E, F, E, F], [E, E, T, E, F, E, T, T, E, E, E, E, F, E, F]), ([E, E, T, E, T, F, E, E, T, E, E, E, F, E, F], [E, E, T, E, T, F, E, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_772 (And.intro z_958 (And.intro z_983 trivial)))

theorem z_985 : le (tf [E, E, T, E, T, T, F, E, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, T, F, E, E, E, E, E, F, E, F] [([E, E, E, T, T, T, F, E, E, E, E, E, F, E, F], [E, E, E, T, T, T, F, E, E, E, E, F, E, E, F]), ([E, E, T, E, T, E, F, T, E, E, E, E, F, E, F], [E, E, T, E, T, F, E, T, E, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_773 (And.intro z_984 trivial))

theorem z_986 : le (tf [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F] [([F, E, E, E, T, E, T, E, E, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 trivial)

theorem z_987 : le (tf [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F] [([F, E, E, E, T, E, T, E, E, E, E, T, F, E, F], [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F]), ([F, E, E, E, T, T, E, E, E, E, E, E, F, T, F], [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 (And.intro z_986 trivial))

theorem z_988 : le (tf [F, E, E, E, T, T, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, E, T, E, E, F, F] [([F, E, E, E, T, E, T, E, E, E, T, E, E, F, F], [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F]), ([F, E, E, E, T, T, E, E, E, E, E, T, E, F, F], [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_793 (And.intro z_987 trivial))

theorem z_989 : le (tf [E, F, E, E, T, T, E, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, T, E, E, E, F, F] [([E, F, E, E, T, E, T, E, E, T, E, E, E, F, F], [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F]), ([E, F, E, E, T, T, E, E, E, E, T, E, E, F, F], [F, E, E, E, T, T, E, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_794 (And.intro z_988 trivial))

theorem z_990 : le (tf [E, E, F, E, T, T, E, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, T, E, E, E, E, F, F] [([E, E, F, E, T, E, T, E, T, E, E, E, E, F, F], [E, E, F, E, T, E, T, E, T, E, E, E, F, E, F]), ([E, E, F, E, T, T, E, E, E, T, E, E, E, F, F], [E, F, E, E, T, T, E, E, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_795 (And.intro z_989 trivial))

theorem z_991 : le (tf [E, F, E, E, T, T, E, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, E, T, E, F, E, F] [([E, F, E, E, T, E, T, E, E, E, T, E, F, E, F], [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F]), ([E, F, E, E, T, T, E, E, E, E, E, T, F, E, F], [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_793 (And.intro z_987 trivial))

theorem z_992 : le (tf [E, E, F, E, T, T, E, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, E, T, E, E, F, E, F] [([E, E, F, E, T, E, T, E, E, T, E, E, F, E, F], [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F]), ([E, E, F, E, T, T, E, E, E, E, T, E, F, E, F], [E, F, E, E, T, T, E, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_794 (And.intro z_991 trivial))

theorem z_993 : le (tf [E, F, E, E, T, T, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, E, E, F, T, E, F] [([E, F, E, E, T, E, T, E, E, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, E, E, F, T, E, F]), ([E, F, E, E, T, T, E, E, E, E, E, F, E, T, F], [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_860 (And.intro z_986 trivial))

theorem z_994 : le (tf [E, E, F, E, T, T, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, E, E, T, F, E, E, F] [([E, E, F, E, T, E, T, E, E, E, T, F, E, E, F], [E, F, E, E, T, E, T, E, E, E, T, F, E, E, F]), ([E, E, F, E, T, T, E, E, E, E, E, F, T, E, F], [E, F, E, E, T, T, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_861 (And.intro z_993 trivial))

theorem z_995 : le (tf [F, E, E, E, T, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, E, E, F, E, T, E, F] [([F, E, E, E, T, E, T, E, E, E, F, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F]), ([F, E, E, E, T, T, E, E, E, E, F, E, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_968 trivial))

theorem z_996 : le (tf [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F] [([F, E, E, E, T, T, E, E, E, E, F, E, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F]), ([F, E, E, T, E, E, T, E, E, E, F, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_968 (And.intro z_962 trivial))

theorem z_997 : le (tf [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F] [([F, E, E, E, T, T, E, E, E, E, E, F, T, E, F], [F, E, E, E, T, T, E, E, E, E, F, E, T, E, F]), ([F, E, E, T, E, E, T, E, E, E, E, F, T, E, F], [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F]), ([F, E, E, T, E, T, E, E, E, E, E, F, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_995 (And.intro z_963 (And.intro z_996 trivial)))

theorem z_998 : le (tf [F, E, T, E, E, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, T, E, E, E, E, E, F, E, T, F] [([F, E, E, T, E, T, E, E, E, E, E, F, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F]), ([F, E, T, E, E, E, T, E, E, E, E, F, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_996 (And.intro z_964 trivial))

theorem z_999 : le (tf [E, F, T, E, E, T, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, E, E, E, F, T, E, F] [([E, F, E, T, E, T, E, E, E, E, E, F, T, E, F], [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F]), ([E, F, T, E, E, E, T, E, E, E, E, F, T, E, F], [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F]), ([E, F, T, E, E, T, E, E, E, E, E, F, E, T, F], [F, E, T, E, E, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_997 (And.intro z_965 (And.intro z_998 trivial)))

theorem z_1000 : le (tf [E, E, T, F, E, T, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, E, E, T, F, E, E, F] [([E, E, E, F, T, T, E, E, E, E, T, F, E, E, F], [E, E, F, E, T, T, E, E, E, E, T, F, E, E, F]), ([E, E, T, F, E, E, T, E, E, E, T, F, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F]), ([E, E, T, F, E, T, E, E, E, E, E, F, T, E, F], [E, F, T, E, E, T, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_994 (And.intro z_955 (And.intro z_999 trivial)))

theorem z_1001 : le (tf [E, E, T, F, E, T, E, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, E, T, E, E, F, E, F] [([E, E, E, F, T, T, E, E, E, T, E, E, F, E, F], [E, E, F, E, T, T, E, E, E, T, E, E, F, E, F]), ([E, E, T, F, E, E, T, E, E, T, E, E, F, E, F], [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F]), ([E, E, T, F, E, T, E, E, E, E, T, E, F, E, F], [E, E, T, F, E, T, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_992 (And.intro z_956 (And.intro z_1000 trivial)))

theorem z_1002 : le (tf [E, E, T, F, E, T, E, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, T, E, E, E, E, F, F] [([E, E, E, F, T, T, E, E, T, E, E, E, E, F, F], [E, E, F, E, T, T, E, E, T, E, E, E, E, F, F]), ([E, E, T, F, E, E, T, E, T, E, E, E, E, F, F], [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F]), ([E, E, T, F, E, T, E, E, E, T, E, E, E, F, F], [E, E, T, F, E, T, E, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_990 (And.intro z_957 (And.intro z_1001 trivial)))

theorem z_1003 : le (tf [E, F, E, E, T, T, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, E, E, F, E, E, T, F] [([E, F, E, E, T, E, T, E, E, E, F, E, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 trivial)

theorem z_1004 : le (tf [E, E, F, E, T, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, E, E, F, E, T, E, F] [([E, E, F, E, T, E, T, E, E, E, F, E, T, E, F], [E, F, E, E, T, E, T, E, E, E, F, E, T, E, F]), ([E, E, F, E, T, T, E, E, E, E, F, E, E, T, F], [E, F, E, E, T, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_960 (And.intro z_1003 trivial))

theorem z_1005 : le (tf [E, F, T, E, E, T, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, E, E, F, E, E, T, F] [([E, F, E, T, E, T, E, E, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F]), ([E, F, T, E, E, E, T, E, E, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_996 (And.intro z_964 trivial))

theorem z_1006 : le (tf [E, E, T, F, E, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, E, E, F, E, T, E, F] [([E, E, E, F, T, T, E, E, E, E, F, E, T, E, F], [E, E, F, E, T, T, E, E, E, E, F, E, T, E, F]), ([E, E, T, F, E, E, T, E, E, E, F, E, T, E, F], [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F]), ([E, E, T, F, E, T, E, E, E, E, F, E, E, T, F], [E, F, T, E, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1004 (And.intro z_965 (And.intro z_1005 trivial)))

theorem z_1007 : le (tf [E, F, E, E, T, E, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, E, E, F, E, E, E, T, F] [([E, F, E, E, E, T, T, E, E, F, E, E, E, T, F], [F, E, E, E, E, T, T, E, E, F, E, E, E, T, F]), ([E, F, E, E, T, E, E, T, E, F, E, E, E, T, F], [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 (And.intro z_784 trivial))

theorem z_1008 : le (tf [E, E, F, E, T, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, E, F, E, E, E, T, F] [([E, E, F, E, T, E, T, E, E, F, E, E, E, T, F], [E, F, E, E, T, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1007 trivial)

theorem z_1009 : le (tf [E, F, T, E, E, E, T, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, E, E, F, E, E, E, T, F] [([E, F, E, T, E, E, T, E, E, F, E, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F]), ([E, F, T, E, E, E, E, T, E, F, E, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_962 (And.intro z_854 trivial))

theorem z_1010 : le (tf [E, E, T, F, E, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, E, F, E, E, E, T, F] [([E, E, E, F, T, T, E, E, E, F, E, E, E, T, F], [E, E, F, E, T, T, E, E, E, F, E, E, E, T, F]), ([E, E, T, F, E, E, T, E, E, F, E, E, E, T, F], [E, F, T, E, E, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1008 (And.intro z_1009 trivial))

theorem z_1011 : le (tf [E, E, T, T, F, E, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, F, E, E, E, T, F] [([E, E, T, E, F, T, E, E, E, F, E, E, E, T, F], [E, E, T, F, E, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1010 trivial)

theorem z_1012 : le (tf [E, E, T, T, F, E, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, E, F, E, T, E, F] [([E, E, T, E, F, T, E, E, E, E, F, E, T, E, F], [E, E, T, F, E, T, E, E, E, E, F, E, T, E, F]), ([E, E, T, T, F, E, E, E, E, E, F, E, E, T, F], [E, E, T, T, F, E, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1006 (And.intro z_1011 trivial))

theorem z_1013 : le (tf [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F] [([E, E, T, E, F, T, E, E, E, E, T, F, E, E, F], [E, E, T, F, E, T, E, E, E, E, T, F, E, E, F]), ([E, E, T, T, F, E, E, E, E, E, E, F, T, E, F], [E, E, T, T, F, E, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1000 (And.intro z_1012 trivial))

theorem z_1014 : le (tf [E, E, T, T, F, E, E, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, T, E, E, F, E, F] [([E, E, T, E, F, T, E, E, E, T, E, E, F, E, F], [E, E, T, F, E, T, E, E, E, T, E, E, F, E, F]), ([E, E, T, T, F, E, E, E, E, E, T, E, F, E, F], [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1001 (And.intro z_1013 trivial))

theorem z_1015 : le (tf [E, E, T, T, F, E, E, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, T, E, E, E, E, F, F] [([E, E, T, E, F, T, E, E, T, E, E, E, E, F, F], [E, E, T, F, E, T, E, E, T, E, E, E, E, F, F]), ([E, E, T, T, F, E, E, E, E, T, E, E, E, F, F], [E, E, T, T, F, E, E, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1002 (And.intro z_1014 trivial))

theorem z_1016 : le (tf [E, E, T, T, E, F, E, T, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, E, F, E, T, E, E, E, E, E, F, F] [([E, E, T, E, T, F, E, T, E, E, E, E, E, F, F], [E, E, T, E, T, F, E, T, E, E, E, E, F, E, F]), ([E, E, T, T, E, F, E, E, T, E, E, E, E, F, F], [E, E, T, T, F, E, E, E, T, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_984 (And.intro z_1015 trivial))

theorem z_1017 : le (tf [E, E, T, T, E, T, F, E, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, E, T, F, E, E, E, E, E, E, F, F] [([E, E, T, E, T, T, F, E, E, E, E, E, E, F, F], [E, E, T, E, T, T, F, E, E, E, E, E, F, E, F]), ([E, E, T, T, E, E, F, T, E, E, E, E, E, F, F], [E, E, T, T, E, F, E, T, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_985 (And.intro z_1016 trivial))

theorem z_1018 : le (tf [E, E, T, T, T, E, E, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, T, E, E, F, E, E, E, E, E, F, F] [([E, E, T, T, E, T, E, F, E, E, E, E, E, F, F], [E, E, T, T, E, T, F, E, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1017 trivial)

theorem z_1019 : le (tf [E, F, E, T, E, E, E, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, T, T, E, F, E, E, F] [([E, F, E, E, T, E, E, E, T, T, E, F, E, E, F], [F, E, E, E, T, E, E, E, T, T, E, F, E, E, F]), ([E, F, E, T, E, E, E, E, T, E, T, F, E, E, F], [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_774 (And.intro z_527 trivial))

theorem z_1020 : le (tf [F, E, E, E, T, E, E, E, F, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, E, T, T, F, E] [([F, E, E, E, E, T, E, E, F, E, E, T, T, F, E], [F, E, E, E, E, T, E, F, E, E, E, T, T, F, E]), ([F, E, E, E, T, E, E, E, F, E, E, T, E, F, T], [F, E, E, E, T, E, E, F, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_806 (And.intro z_815 trivial))

theorem z_1021 : le (tf [F, E, E, T, E, E, E, F, E, E, E, E, T, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, E, E, T, F, T] [([F, E, E, E, T, E, E, F, E, E, E, E, T, F, T], [F, E, E, E, T, E, F, E, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_814 trivial)

theorem z_1022 : le (tf [F, E, E, T, E, E, E, E, F, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, E, T, E, F, T] [([F, E, E, E, T, E, E, E, F, E, E, T, E, F, T], [F, E, E, E, T, E, E, F, E, E, E, T, E, F, T]), ([F, E, E, T, E, E, E, E, F, E, E, E, T, F, T], [F, E, E, T, E, E, E, F, E, E, E, E, T, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_815 (And.intro z_1021 trivial))

theorem z_1023 : le (tf [F, E, E, T, E, E, E, E, E, F, E, T, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, F, E, T, T, F, E] [([F, E, E, E, T, E, E, E, E, F, E, T, T, F, E], [F, E, E, E, T, E, E, E, F, E, E, T, T, F, E]), ([F, E, E, T, E, E, E, E, E, F, E, T, E, F, T], [F, E, E, T, E, E, E, E, F, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1020 (And.intro z_1022 trivial))

theorem z_1024 : le (tf [F, E, E, T, E, E, E, E, F, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, E, E, E, F, T] [([F, E, E, E, T, E, E, E, F, T, E, E, E, F, T], [F, E, E, E, T, E, E, F, E, T, E, E, E, F, T]), ([F, E, E, T, E, E, E, E, F, E, T, E, E, F, T], [F, E, E, T, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_494 (And.intro z_841 trivial))

theorem z_1025 : le (tf [F, E, E, T, E, E, E, E, E, T, F, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, T, F, E, T, F, E] [([F, E, E, E, T, E, E, E, E, T, F, E, T, F, E], [F, E, E, E, T, E, E, E, F, T, E, E, T, F, E]), ([F, E, E, T, E, E, E, E, E, E, F, T, T, F, E], [F, E, E, T, E, E, E, E, E, F, E, T, T, F, E]), ([F, E, E, T, E, E, E, E, E, T, F, E, E, F, T], [F, E, E, T, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_495 (And.intro z_1023 (And.intro z_1024 trivial)))

theorem z_1026 : le (tf [F, E, E, T, E, E, F, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, E, E, F, T, T] [([F, E, E, E, T, E, F, E, E, E, E, E, F, T, T], [F, E, E, E, T, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_776 trivial)

theorem z_1027 : le (tf [F, E, E, T, E, E, E, F, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, E, E, T, F, E, T] [([F, E, E, E, T, E, E, F, E, E, E, T, F, E, T], [F, E, E, E, T, E, F, E, E, E, E, T, F, E, T]), ([F, E, E, T, E, E, E, F, E, E, E, E, F, T, T], [F, E, E, T, E, E, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_777 (And.intro z_1026 trivial))

theorem z_1028 : le (tf [F, E, E, T, E, E, E, E, F, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, E, T, F, T, E] [([F, E, E, E, T, E, E, E, F, E, E, T, F, T, E], [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E]), ([F, E, E, T, E, E, E, E, F, E, E, T, F, E, T], [F, E, E, T, E, E, E, F, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_778 (And.intro z_1027 trivial))

theorem z_1029 : le (tf [F, E, E, T, E, E, E, E, F, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, T, E, E, T, F] [([F, E, E, E, T, E, E, E, F, E, T, E, E, T, F], [F, E, E, E, T, E, E, F, E, E, T, E, E, T, F]), ([F, E, E, T, E, E, E, E, F, E, E, T, E, T, F], [F, E, E, T, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_780 (And.intro z_1028 trivial))

theorem z_1030 : le (tf [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F] [([F, E, E, E, T, E, E, E, T, F, E, E, E, T, F], [F, E, E, E, T, E, E, F, T, E, E, E, E, T, F]), ([F, E, E, T, E, E, E, E, E, F, T, E, E, T, F], [F, E, E, T, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_782 (And.intro z_1029 trivial))

theorem z_1031 : le (tf [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F] [([F, E, E, E, T, E, E, E, T, E, F, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F]), ([F, E, E, T, E, E, E, E, E, T, F, E, T, E, F], [F, E, E, T, E, E, E, E, E, T, F, E, T, F, E]), ([F, E, E, T, E, E, E, E, T, E, F, E, E, T, F], [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_783 (And.intro z_1025 (And.intro z_1030 trivial)))

theorem z_1032 : le (tf [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F] [([F, E, E, E, T, E, E, T, E, E, F, E, E, T, F], [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F]), ([F, E, E, T, E, E, E, E, T, E, F, E, E, T, F], [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_784 (And.intro z_1030 trivial))

theorem z_1033 : le (tf [F, E, E, T, E, E, E, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, E, E, F, T, E, F] [([F, E, E, E, T, E, E, T, E, E, E, F, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F]), ([F, E, E, T, E, E, E, E, T, E, E, F, T, E, F], [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F]), ([F, E, E, T, E, E, E, T, E, E, E, F, E, T, F], [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_785 (And.intro z_1031 (And.intro z_1032 trivial)))

theorem z_1034 : le (tf [E, F, E, T, E, E, E, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, E, E, T, F, E, E, F] [([E, F, E, E, T, E, E, T, E, E, T, F, E, E, F], [F, E, E, E, T, E, E, T, E, E, T, F, E, E, F]), ([E, F, E, T, E, E, E, E, T, E, T, F, E, E, F], [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F]), ([E, F, E, T, E, E, E, T, E, E, E, F, T, E, F], [F, E, E, T, E, E, E, T, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_786 (And.intro z_527 (And.intro z_1033 trivial)))

theorem z_1035 : le (tf [E, F, E, T, E, E, E, T, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, E, T, E, E, F, E, F] [([E, F, E, E, T, E, E, T, E, T, E, E, F, E, F], [F, E, E, E, T, E, E, T, E, T, E, E, F, E, F]), ([E, F, E, T, E, E, E, E, T, T, E, E, F, E, F], [E, F, E, T, E, E, E, E, T, T, E, F, E, E, F]), ([E, F, E, T, E, E, E, T, E, E, T, E, F, E, F], [E, F, E, T, E, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_787 (And.intro z_1019 (And.intro z_1034 trivial)))

theorem z_1036 : le (tf [E, F, E, T, E, E, E, T, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, T, E, E, E, E, F, F] [([E, F, E, E, T, E, E, T, T, E, E, E, E, F, F], [E, F, E, E, T, E, E, T, T, E, E, E, F, E, F]), ([E, F, E, T, E, E, E, T, E, T, E, E, E, F, F], [E, F, E, T, E, E, E, T, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_788 (And.intro z_1035 trivial))

theorem z_1037 : le (tf [E, F, E, T, E, E, F, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, E, T, F, T, E, E] [([E, F, E, E, T, E, F, E, E, E, T, F, T, E, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]), ([E, F, E, T, E, E, F, E, E, E, T, F, E, T, E], [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_473 (And.intro z_512 trivial))

theorem z_1038 : le (tf [E, F, E, T, E, E, F, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, E, T, T, E, F, E] [([E, F, E, E, T, E, F, E, E, E, T, T, E, F, E], [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]), ([E, F, E, T, E, E, F, E, E, E, T, E, T, F, E], [E, F, E, T, E, E, F, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_474 (And.intro z_1037 trivial))

theorem z_1039 : le (tf [E, F, E, T, E, E, F, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, T, E, E, T, F, E] [([E, F, E, E, T, E, F, E, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]), ([E, F, E, T, E, E, F, E, E, E, T, E, T, F, E], [E, F, E, T, E, E, F, E, E, E, T, F, T, E, E]), ([E, F, E, T, E, E, F, E, E, T, E, E, E, F, T], [F, E, E, T, E, E, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_1037 (And.intro z_516 trivial)))

theorem z_1040 : le (tf [E, F, E, T, E, E, F, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, T, E, T, E, E, F] [([E, F, E, E, T, E, F, E, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F]), ([E, F, E, T, E, E, F, E, E, E, T, T, E, E, F], [E, F, E, T, E, E, F, E, E, E, T, T, E, F, E]), ([E, F, E, T, E, E, F, E, E, T, E, E, T, E, F], [E, F, E, T, E, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_1038 (And.intro z_1039 trivial)))

theorem z_1041 : le (tf [E, F, E, T, E, F, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, E, E, T, F, E, T, E] [([E, F, E, E, T, F, E, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]), ([E, F, E, T, E, F, E, E, E, E, E, F, T, T, E], [F, E, E, T, E, F, E, E, E, E, E, F, T, T, E]), ([E, F, E, T, E, F, E, E, E, E, T, F, E, E, T], [F, E, E, T, E, F, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_472 (And.intro z_510 (And.intro z_511 trivial)))

theorem z_1042 : le (tf [F, T, E, F, E, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, E, E, F, E, T, T] [([F, E, T, F, E, E, E, E, E, E, E, F, E, T, T], [F, F, T, E, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_899 trivial)

theorem z_1043 : le (tf [F, T, E, E, F, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, E, E, F, T, E, T] [([F, E, T, E, F, E, E, E, E, E, E, F, T, E, T], [F, E, T, F, E, E, E, E, E, E, E, F, T, E, T]), ([F, T, E, E, F, E, E, E, E, E, E, F, E, T, T], [F, T, E, F, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_900 (And.intro z_1042 trivial))

theorem z_1044 : le (tf [F, T, E, E, E, F, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, E, F, T, T, E] [([F, E, T, E, E, F, E, E, E, E, E, F, T, T, E], [F, E, T, E, F, E, E, E, E, E, E, F, T, T, E]), ([F, T, E, E, E, F, E, E, E, E, E, F, T, E, T], [F, T, E, E, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_901 (And.intro z_1043 trivial))

theorem z_1045 : le (tf [F, T, E, E, E, F, E, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, T, F, E, E, T] [([F, E, T, E, E, F, E, E, E, E, T, F, E, E, T], [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T]), ([F, T, E, E, E, F, E, E, E, E, E, F, T, E, T], [F, T, E, E, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_902 (And.intro z_1043 trivial))

theorem z_1046 : le (tf [E, T, F, E, E, F, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, E, E, E, T, F, E, T, E] [([E, E, F, T, E, F, E, E, E, E, T, F, E, T, E], [E, F, E, T, E, F, E, E, E, E, T, F, E, T, E]), ([E, T, F, E, E, F, E, E, E, E, E, F, T, T, E], [F, T, E, E, E, F, E, E, E, E, E, F, T, T, E]), ([E, T, F, E, E, F, E, E, E, E, T, F, E, E, T], [F, T, E, E, E, F, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1041 (And.intro z_1044 (And.intro z_1045 trivial)))

theorem z_1047 : le (tf [E, T, F, E, E, E, F, E, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, E, T, F, T, E, E] [([E, E, F, T, E, E, F, E, E, E, T, F, T, E, E], [E, F, E, T, E, E, F, E, E, E, T, F, T, E, E]), ([E, T, F, E, E, E, F, E, E, E, T, F, E, T, E], [E, T, F, E, E, F, E, E, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1037 (And.intro z_1046 trivial))

theorem z_1048 : le (tf [E, T, F, E, E, E, F, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, E, T, T, E, F, E] [([E, E, F, T, E, E, F, E, E, E, T, T, E, F, E], [E, F, E, T, E, E, F, E, E, E, T, T, E, F, E]), ([E, T, F, E, E, E, F, E, E, E, T, E, T, F, E], [E, T, F, E, E, E, F, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1038 (And.intro z_1047 trivial))

theorem z_1049 : le (tf [F, E, T, E, E, F, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, T, E, E, E, F, T] [([F, E, E, T, E, F, E, E, E, T, E, E, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, E, E, F, T]), ([F, E, T, E, E, F, E, E, E, E, T, E, E, F, T], [F, E, T, E, F, E, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_907 (And.intro z_908 trivial))

theorem z_1050 : le (tf [F, T, E, E, F, E, E, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, E, E, T, E, F, T] [([F, E, T, E, F, E, E, E, E, E, E, T, E, F, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T]), ([F, T, E, E, F, E, E, E, E, E, E, E, T, F, T], [F, T, E, E, F, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_849 (And.intro z_1043 trivial))

theorem z_1051 : le (tf [F, T, E, E, E, F, E, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, T, E, E, F, T] [([F, E, T, E, E, F, E, E, E, E, T, E, E, F, T], [F, E, T, E, F, E, E, E, E, E, T, E, E, F, T]), ([F, T, E, E, E, F, E, E, E, E, E, T, E, F, T], [F, T, E, E, F, E, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_908 (And.intro z_1050 trivial))

theorem z_1052 : le (tf [F, T, E, E, E, E, F, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, T, E, E, E, F, T] [([F, E, T, E, E, E, F, E, E, T, E, E, E, F, T], [F, E, T, E, E, F, E, E, E, T, E, E, E, F, T]), ([F, T, E, E, E, E, F, E, E, E, T, E, E, F, T], [F, T, E, E, E, F, E, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1049 (And.intro z_1051 trivial))

theorem z_1053 : le (tf [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E] [([E, E, F, T, E, E, F, E, E, T, E, E, T, F, E], [E, F, E, T, E, E, F, E, E, T, E, E, T, F, E]), ([E, T, F, E, E, E, F, E, E, E, T, E, T, F, E], [E, T, F, E, E, E, F, E, E, E, T, F, T, E, E]), ([E, T, F, E, E, E, F, E, E, T, E, E, E, F, T], [F, T, E, E, E, E, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1039 (And.intro z_1047 (And.intro z_1052 trivial)))

theorem z_1054 : le (tf [E, T, F, E, E, E, F, E, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, T, E, T, E, E, F] [([E, E, F, T, E, E, F, E, E, T, E, T, E, E, F], [E, F, E, T, E, E, F, E, E, T, E, T, E, E, F]), ([E, T, F, E, E, E, F, E, E, E, T, T, E, E, F], [E, T, F, E, E, E, F, E, E, E, T, T, E, F, E]), ([E, T, F, E, E, E, F, E, E, T, E, E, T, E, F], [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1040 (And.intro z_1048 (And.intro z_1053 trivial)))

theorem z_1055 : le (tf [E, F, E, T, E, E, F, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, T, E, E, E, T, E, F] [([E, F, E, E, T, E, F, E, T, E, E, E, T, E, F], [F, E, E, E, T, E, F, E, T, E, E, E, T, E, F]), ([E, F, E, T, E, E, F, E, E, T, E, E, T, E, F], [E, F, E, T, E, E, F, E, E, T, E, E, T, F, E]), ([E, F, E, T, E, E, F, E, T, E, E, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 (And.intro z_1039 (And.intro z_524 trivial)))

theorem z_1056 : le (tf [E, F, E, T, E, F, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, T, E, E, E, E, T, F] [([E, F, E, E, T, F, E, E, T, E, E, E, E, T, F], [F, E, E, E, T, F, E, E, T, E, E, E, E, T, F]), ([E, F, E, T, E, F, E, E, E, T, E, E, E, T, F], [F, E, E, T, E, F, E, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_482 (And.intro z_523 trivial))

theorem z_1057 : le (tf [E, F, E, T, F, E, E, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, T, E, E, E, T, F] [([E, F, E, E, F, T, E, E, E, T, E, E, E, T, F], [F, E, E, E, F, T, E, E, E, T, E, E, E, T, F]), ([E, F, E, T, F, E, E, E, E, E, T, E, E, T, F], [F, E, E, T, F, E, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_247 (And.intro z_522 trivial))

theorem z_1058 : le (tf [F, E, F, E, T, E, E, E, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, T, E, E, E, F, E, E, E, E, T, T] [([F, E, F, E, E, T, E, E, F, E, E, E, E, T, T], [F, F, E, E, E, T, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_384 trivial)

theorem z_1059 : le (tf [F, E, T, F, E, E, E, E, F, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, F, E, E, E, E, T, T] [([F, E, E, F, T, E, E, E, F, E, E, E, E, T, T], [F, E, F, E, T, E, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1058 trivial)

theorem z_1060 : le (tf [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T] [([F, E, E, F, T, E, E, E, E, F, E, E, T, E, T], [F, E, F, E, T, E, E, E, E, F, E, E, T, E, T]), ([F, E, T, F, E, E, E, E, E, F, E, E, E, T, T], [F, E, T, F, E, E, E, E, F, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_469 (And.intro z_1059 trivial))

theorem z_1061 : le (tf [F, E, T, F, E, E, E, E, E, E, F, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, E, F, T, E, E, T] [([F, E, E, F, T, E, E, E, E, E, F, T, E, E, T], [F, E, E, F, T, E, E, E, E, F, E, T, E, E, T]), ([F, E, T, F, E, E, E, E, E, E, F, E, T, E, T], [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_470 (And.intro z_1060 trivial))

theorem z_1062 : le (tf [F, T, E, F, E, E, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, E, E, T, F, E, T] [([F, E, T, F, E, E, E, E, E, E, E, T, F, E, T], [F, E, T, F, E, E, E, E, E, E, F, T, E, E, T]), ([F, T, E, F, E, E, E, E, E, E, E, E, F, T, T], [F, T, E, F, E, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1061 (And.intro z_1042 trivial))

theorem z_1063 : le (tf [E, T, F, F, E, E, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, E, E, T, F, T, E] [([E, T, F, F, E, E, E, E, E, E, E, T, F, E, T], [F, T, E, F, E, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1062 trivial)

theorem z_1064 : le (tf [E, T, F, F, E, E, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, E, T, E, E, T, F] [([E, T, F, F, E, E, E, E, E, E, E, T, E, T, F], [E, T, F, F, E, E, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1063 trivial)

theorem z_1065 : le (tf [E, T, F, E, F, E, E, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, E, T, E, E, E, T, F] [([E, E, F, T, F, E, E, E, E, T, E, E, E, T, F], [E, F, E, T, F, E, E, E, E, T, E, E, E, T, F]), ([E, T, F, E, F, E, E, E, E, E, T, E, E, T, F], [E, T, F, F, E, E, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1057 (And.intro z_1064 trivial))

theorem z_1066 : le (tf [E, T, F, E, E, F, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, E, T, E, E, E, E, T, F] [([E, E, F, T, E, F, E, E, T, E, E, E, E, T, F], [E, F, E, T, E, F, E, E, T, E, E, E, E, T, F]), ([E, T, F, E, E, F, E, E, E, T, E, E, E, T, F], [E, T, F, E, F, E, E, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1056 (And.intro z_1065 trivial))

theorem z_1067 : le (tf [E, T, F, E, E, E, F, E, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, T, E, E, E, T, E, F] [([E, E, F, T, E, E, F, E, T, E, E, E, T, E, F], [E, F, E, T, E, E, F, E, T, E, E, E, T, E, F]), ([E, T, F, E, E, E, F, E, E, T, E, E, T, E, F], [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E]), ([E, T, F, E, E, E, F, E, T, E, E, E, E, T, F], [E, T, F, E, E, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1055 (And.intro z_1053 (And.intro z_1066 trivial)))

theorem z_1068 : le (tf [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F] [([E, E, F, T, E, E, E, F, T, E, E, T, E, E, F], [E, F, E, T, E, E, E, F, T, E, E, T, E, E, F]), ([E, T, F, E, E, E, E, F, E, T, E, T, E, E, F], [E, T, F, E, E, E, F, E, E, T, E, T, E, E, F]), ([E, T, F, E, E, E, E, F, T, E, E, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_743 (And.intro z_1054 (And.intro z_1067 trivial)))

theorem z_1069 : le (tf [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F] [([E, E, F, T, E, E, E, E, T, F, T, E, E, E, F], [E, F, E, T, E, E, E, E, T, F, T, E, E, E, F]), ([E, T, F, E, E, E, E, E, T, F, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_527 (And.intro z_1068 trivial))

theorem z_1070 : le (tf [E, T, F, E, E, E, E, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, T, T, E, F, E, E, F] [([E, E, F, T, E, E, E, E, T, T, E, F, E, E, F], [E, F, E, T, E, E, E, E, T, T, E, F, E, E, F]), ([E, T, F, E, E, E, E, E, T, E, T, F, E, E, F], [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1019 (And.intro z_1069 trivial))

theorem z_1071 : le (tf [E, F, E, T, E, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, E, E, F, E, T, E, F] [([E, F, E, E, T, E, E, T, E, E, F, E, T, E, F], [F, E, E, E, T, E, E, T, E, E, F, E, T, E, F]), ([E, F, E, T, E, E, E, E, T, E, F, E, T, E, F], [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F]), ([E, F, E, T, E, E, E, T, E, E, F, E, E, T, F], [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_785 (And.intro z_1031 (And.intro z_1032 trivial)))

theorem z_1072 : le (tf [F, E, E, T, E, E, E, E, E, F, T, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, F, T, E, T, E, F] [([F, E, E, E, T, E, E, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F]), ([F, E, E, T, E, E, E, E, E, F, E, T, T, E, F], [F, E, E, T, E, E, E, E, E, F, E, T, T, F, E]), ([F, E, E, T, E, E, E, E, E, F, T, E, E, T, F], [F, E, E, T, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_781 (And.intro z_1023 (And.intro z_1029 trivial)))

theorem z_1073 : le (tf [E, F, E, T, E, E, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, T, F, E, E, T, E, F] [([E, F, E, E, T, E, E, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F]), ([E, F, E, T, E, E, E, E, E, F, T, E, T, E, F], [F, E, E, T, E, E, E, E, E, F, T, E, T, E, F]), ([E, F, E, T, E, E, E, E, T, F, E, E, E, T, F], [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_783 (And.intro z_1072 (And.intro z_1030 trivial)))

theorem z_1074 : le (tf [F, E, E, T, E, E, E, E, F, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, E, E, T, T, E, F] [([F, E, E, E, T, E, E, E, F, E, E, T, T, E, F], [F, E, E, E, T, E, E, F, E, E, E, T, T, E, F]), ([F, E, E, T, E, E, E, E, F, E, E, T, E, T, F], [F, E, E, T, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_779 (And.intro z_1028 trivial))

theorem z_1075 : le (tf [E, F, E, T, E, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, E, T, E, T, E, F] [([E, F, E, E, T, E, E, E, F, E, T, E, T, E, F], [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F]), ([E, F, E, T, E, E, E, E, F, E, E, T, T, E, F], [F, E, E, T, E, E, E, E, F, E, E, T, T, E, F]), ([E, F, E, T, E, E, E, E, F, E, T, E, E, T, F], [F, E, E, T, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_781 (And.intro z_1074 (And.intro z_1029 trivial)))

theorem z_1076 : le (tf [F, E, E, T, E, E, F, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, E, E, T, T, E, F] [([F, E, E, E, T, E, F, E, E, E, E, T, T, E, F], [F, E, E, E, T, F, E, E, E, E, E, T, T, E, F]), ([F, E, E, T, E, E, F, E, E, E, E, T, E, T, F], [F, E, E, T, E, E, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_943 (And.intro z_533 trivial))

theorem z_1077 : le (tf [F, E, T, E, E, F, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, E, E, F, T, T] [([F, E, E, T, E, F, E, E, E, E, E, E, F, T, T], [F, E, E, T, E, F, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 trivial)

theorem z_1078 : le (tf [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T] [([F, E, E, T, E, E, F, E, E, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, E, E, T, F, E, T]), ([F, E, T, E, E, E, F, E, E, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_532 (And.intro z_1077 trivial))

theorem z_1079 : le (tf [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E] [([F, E, E, T, E, E, E, F, E, E, E, T, F, T, E], [F, E, E, T, E, E, F, E, E, E, E, T, F, T, E]), ([F, E, T, E, E, E, E, F, E, E, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_533 (And.intro z_1078 trivial))

theorem z_1080 : le (tf [F, E, T, E, E, E, E, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, E, T, T, E, F] [([F, E, E, T, E, E, E, F, E, E, E, T, T, E, F], [F, E, E, T, E, E, F, E, E, E, E, T, T, E, F]), ([F, E, T, E, E, E, E, F, E, E, E, T, E, T, F], [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1076 (And.intro z_1079 trivial))

theorem z_1081 : le (tf [F, T, E, E, E, E, F, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, E, E, F, T, T] [([F, E, T, E, E, E, F, E, E, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1077 trivial)

theorem z_1082 : le (tf [F, T, E, E, E, E, E, F, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, E, E, T, F, E, T] [([F, E, T, E, E, E, E, F, E, E, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T]), ([F, T, E, E, E, E, E, F, E, E, E, E, F, T, T], [F, T, E, E, E, E, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1078 (And.intro z_1081 trivial))

theorem z_1083 : le (tf [F, T, E, E, E, E, E, E, F, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, E, E, T, F, T, E] [([F, E, T, E, E, E, E, E, F, E, E, T, F, T, E], [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E]), ([F, T, E, E, E, E, E, E, F, E, E, T, F, E, T], [F, T, E, E, E, E, E, F, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1079 (And.intro z_1082 trivial))

theorem z_1084 : le (tf [F, T, E, E, E, E, E, E, F, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, E, E, T, T, E, F] [([F, E, T, E, E, E, E, E, F, E, E, T, T, E, F], [F, E, T, E, E, E, E, F, E, E, E, T, T, E, F]), ([F, T, E, E, E, E, E, E, F, E, E, T, E, T, F], [F, T, E, E, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1080 (And.intro z_1083 trivial))

theorem z_1085 : le (tf [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F] [([F, E, E, T, E, E, E, F, E, E, T, E, E, T, F], [F, E, E, T, E, E, F, E, E, E, T, E, E, T, F]), ([F, E, T, E, E, E, E, F, E, E, E, T, E, T, F], [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_534 (And.intro z_1079 trivial))

theorem z_1086 : le (tf [F, T, E, E, E, E, E, E, F, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, E, T, E, E, T, F] [([F, E, T, E, E, E, E, E, F, E, T, E, E, T, F], [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F]), ([F, T, E, E, E, E, E, E, F, E, E, T, E, T, F], [F, T, E, E, E, E, E, E, F, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1085 (And.intro z_1083 trivial))

theorem z_1087 : le (tf [E, T, F, E, E, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, F, E, T, E, T, E, F] [([E, E, F, T, E, E, E, E, F, E, T, E, T, E, F], [E, F, E, T, E, E, E, E, F, E, T, E, T, E, F]), ([E, T, F, E, E, E, E, E, F, E, E, T, T, E, F], [F, T, E, E, E, E, E, E, F, E, E, T, T, E, F]), ([E, T, F, E, E, E, E, E, F, E, T, E, E, T, F], [F, T, E, E, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1075 (And.intro z_1084 (And.intro z_1086 trivial)))

theorem z_1088 : le (tf [F, T, E, E, E, E, E, E, T, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, T, F, E, E, E, T, F] [([F, E, T, E, E, E, E, E, T, F, E, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F]), ([F, T, E, E, E, E, E, E, E, F, T, E, E, T, F], [F, T, E, E, E, E, E, E, F, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_853 (And.intro z_1086 trivial))

theorem z_1089 : le (tf [E, T, F, E, E, E, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, T, F, E, E, T, E, F] [([E, E, F, T, E, E, E, E, T, F, E, E, T, E, F], [E, F, E, T, E, E, E, E, T, F, E, E, T, E, F]), ([E, T, F, E, E, E, E, E, E, F, T, E, T, E, F], [E, T, F, E, E, E, E, E, F, E, T, E, T, E, F]), ([E, T, F, E, E, E, E, E, T, F, E, E, E, T, F], [F, T, E, E, E, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1073 (And.intro z_1087 (And.intro z_1088 trivial)))

theorem z_1090 : le (tf [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F] [([F, E, T, E, E, E, E, T, E, E, F, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F]), ([F, T, E, E, E, E, E, E, T, E, F, E, E, T, F], [F, T, E, E, E, E, E, E, T, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_854 (And.intro z_1088 trivial))

theorem z_1091 : le (tf [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F] [([E, E, F, T, E, E, E, T, E, E, F, E, T, E, F], [E, F, E, T, E, E, E, T, E, E, F, E, T, E, F]), ([E, T, F, E, E, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, E, E, T, F, E, E, T, E, F]), ([E, T, F, E, E, E, E, T, E, E, F, E, E, T, F], [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1071 (And.intro z_1089 (And.intro z_1090 trivial)))

theorem z_1092 : le (tf [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F] [([E, E, F, T, E, E, E, T, E, E, T, F, E, E, F], [E, F, E, T, E, E, E, T, E, E, T, F, E, E, F]), ([E, T, F, E, E, E, E, E, T, E, T, F, E, E, F], [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F]), ([E, T, F, E, E, E, E, T, E, E, E, F, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1034 (And.intro z_1069 (And.intro z_1091 trivial)))

theorem z_1093 : le (tf [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F] [([E, E, F, T, E, E, E, T, E, T, E, E, F, E, F], [E, F, E, T, E, E, E, T, E, T, E, E, F, E, F]), ([E, T, F, E, E, E, E, E, T, T, E, E, F, E, F], [E, T, F, E, E, E, E, E, T, T, E, F, E, E, F]), ([E, T, F, E, E, E, E, T, E, E, T, E, F, E, F], [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1035 (And.intro z_1070 (And.intro z_1092 trivial)))

theorem z_1094 : le (tf [E, T, F, E, E, E, E, T, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, T, E, E, E, E, F, F] [([E, E, F, T, E, E, E, T, T, E, E, E, E, F, F], [E, F, E, T, E, E, E, T, T, E, E, E, E, F, F]), ([E, T, F, E, E, E, E, T, E, T, E, E, E, F, F], [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1036 (And.intro z_1093 trivial))

theorem z_1095 : le (tf [F, E, E, T, E, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, E, F, T, E, E, F] [([F, E, E, E, T, E, E, T, E, E, F, T, E, E, F], [F, E, E, E, T, E, E, T, E, F, E, T, E, E, F]), ([F, E, E, T, E, E, E, E, T, E, F, T, E, E, F], [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F]), ([F, E, E, T, E, E, E, T, E, E, F, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 (And.intro z_526 (And.intro z_537 trivial)))

theorem z_1096 : le (tf [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F] [([F, E, E, E, T, E, T, E, E, E, E, F, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F]), ([F, E, E, T, E, E, E, T, E, E, E, F, E, T, F], [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 (And.intro z_1032 trivial))

theorem z_1097 : le (tf [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F] [([F, E, E, E, T, E, T, E, E, E, E, T, F, E, F], [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F]), ([F, E, E, T, E, E, E, T, E, E, E, T, F, E, F], [F, E, E, T, E, E, E, T, E, E, F, T, E, E, F]), ([F, E, E, T, E, E, T, E, E, E, E, E, F, T, F], [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 (And.intro z_1095 (And.intro z_1096 trivial)))

theorem z_1098 : le (tf [E, F, E, T, E, E, T, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, E, T, E, F, E, F] [([E, F, E, E, T, E, T, E, E, E, T, E, F, E, F], [F, E, E, E, T, E, T, E, E, E, T, E, F, E, F]), ([E, F, E, T, E, E, E, T, E, E, T, E, F, E, F], [E, F, E, T, E, E, E, T, E, E, T, F, E, E, F]), ([E, F, E, T, E, E, T, E, E, E, E, T, F, E, F], [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_793 (And.intro z_1034 (And.intro z_1097 trivial)))

theorem z_1099 : le (tf [E, F, E, T, E, E, T, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, T, E, E, E, F, F] [([E, F, E, E, T, E, T, E, E, T, E, E, E, F, F], [E, F, E, E, T, E, T, E, E, T, E, E, F, E, F]), ([E, F, E, T, E, E, E, T, E, T, E, E, E, F, F], [E, F, E, T, E, E, E, T, E, T, E, E, F, E, F]), ([E, F, E, T, E, E, T, E, E, E, T, E, E, F, F], [E, F, E, T, E, E, T, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_794 (And.intro z_1035 (And.intro z_1098 trivial)))

theorem z_1100 : le (tf [E, F, E, T, E, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, E, F, T, E, E, F] [([E, F, E, E, T, E, T, E, E, E, F, T, E, E, F], [F, E, E, E, T, E, T, E, E, E, F, T, E, E, F]), ([E, F, E, T, E, E, E, T, E, E, F, T, E, E, F], [F, E, E, T, E, E, E, T, E, E, F, T, E, E, F]), ([E, F, E, T, E, E, T, E, E, E, F, E, T, E, F], [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_792 (And.intro z_1095 (And.intro z_963 trivial)))

theorem z_1101 : le (tf [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F] [([E, F, E, E, T, E, F, E, E, E, T, E, T, E, F], [E, F, E, E, T, F, E, E, E, E, T, E, T, E, F]), ([E, F, E, T, E, E, F, E, E, E, E, T, T, E, F], [F, E, E, T, E, E, F, E, E, E, E, T, T, E, F]), ([E, F, E, T, E, E, F, E, E, E, T, E, E, T, F], [F, E, E, T, E, E, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_944 (And.intro z_1076 (And.intro z_534 trivial)))

theorem z_1102 : le (tf [E, F, E, T, E, E, E, F, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, T, E, E, T, E, F] [([E, F, E, E, T, E, E, F, E, T, E, E, T, E, F], [E, F, E, E, T, E, F, E, E, T, E, E, T, E, F]), ([E, F, E, T, E, E, E, F, E, E, T, E, T, E, F], [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F]), ([E, F, E, T, E, E, E, F, E, T, E, E, E, T, F], [F, E, E, T, E, E, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_945 (And.intro z_1101 (And.intro z_535 trivial)))

theorem z_1103 : le (tf [E, F, E, T, E, E, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, F, E, E, E, T, E, F] [([E, F, E, E, T, E, E, T, F, E, E, E, T, E, F], [F, E, E, E, T, E, E, T, F, E, E, E, T, E, F]), ([E, F, E, T, E, E, E, E, F, T, E, E, T, E, F], [E, F, E, T, E, E, E, F, E, T, E, E, T, E, F]), ([E, F, E, T, E, E, E, T, F, E, E, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 (And.intro z_1102 (And.intro z_536 trivial)))

theorem z_1104 : le (tf [E, F, E, T, E, F, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, E, E, E, T, F, T, E] [([E, F, E, E, T, F, E, E, E, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E]), ([E, F, E, T, E, F, E, E, E, E, E, T, F, E, T], [F, E, E, T, E, F, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_529 (And.intro z_532 trivial))

theorem z_1105 : le (tf [E, F, E, T, E, F, E, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, E, E, E, E, T, T, E, F] [([E, F, E, E, T, F, E, E, E, E, E, T, T, E, F], [F, E, E, E, T, F, E, E, E, E, E, T, T, E, F]), ([E, F, E, T, E, F, E, E, E, E, E, T, E, T, F], [E, F, E, T, E, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_943 (And.intro z_1104 trivial))

theorem z_1106 : le (tf [E, F, E, E, F, T, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, E, E, E, E, T, F, T, E] [([E, F, E, E, F, E, T, E, E, E, E, T, F, T, E], [F, E, E, E, F, E, T, E, E, E, E, T, F, T, E]), ([E, F, E, E, F, T, E, E, E, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 (And.intro z_202 trivial))

theorem z_1107 : le (tf [F, E, E, T, F, E, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, E, E, E, E, E, F, T, T] [([F, E, E, E, F, T, E, E, E, E, E, E, F, T, T], [F, E, E, F, E, T, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 trivial)

theorem z_1108 : le (tf [E, F, E, T, F, E, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, E, E, T, F, E, T] [([E, F, E, E, F, T, E, E, E, E, E, T, F, E, T], [F, E, E, E, F, T, E, E, E, E, E, T, F, E, T]), ([E, F, E, T, F, E, E, E, E, E, E, E, F, T, T], [F, E, E, T, F, E, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_1107 trivial))

theorem z_1109 : le (tf [E, E, F, T, F, E, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, F, E, E, E, E, E, E, T, F, T, E] [([E, E, F, E, F, T, E, E, E, E, E, T, F, T, E], [E, F, E, E, F, T, E, E, E, E, E, T, F, T, E]), ([E, E, F, T, F, E, E, E, E, E, E, T, F, E, T], [E, F, E, T, F, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1106 (And.intro z_1108 trivial))

theorem z_1110 : le (tf [E, T, F, F, E, E, E, E, E, E, E, E, T, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, E, E, E, T, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1111 : le (tf [E, T, F, E, F, E, E, E, E, E, E, T, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, E, E, E, T, E, T, F] [([E, E, F, T, F, E, E, E, E, E, E, T, E, T, F], [E, E, F, T, F, E, E, E, E, E, E, T, F, T, E]), ([E, T, F, E, F, E, E, E, E, E, E, E, T, T, F], [E, T, F, F, E, E, E, E, E, E, E, E, T, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1109 (And.intro z_1110 trivial))

theorem z_1112 : le (tf [E, T, F, E, E, F, E, E, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, E, E, E, E, T, T, E, F] [([E, E, F, T, E, F, E, E, E, E, E, T, T, E, F], [E, F, E, T, E, F, E, E, E, E, E, T, T, E, F]), ([E, T, F, E, E, F, E, E, E, E, E, T, E, T, F], [E, T, F, E, F, E, E, E, E, E, E, T, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1105 (And.intro z_1111 trivial))

theorem z_1113 : le (tf [F, T, E, E, F, E, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, E, E, E, F, T, T] [([F, E, T, E, F, E, E, E, E, E, E, E, F, T, T], [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_829 trivial)

theorem z_1114 : le (tf [F, T, E, E, E, F, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, E, T, F, E, T] [([F, E, T, E, E, F, E, E, E, E, E, T, F, E, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T]), ([F, T, E, E, E, F, E, E, E, E, E, E, F, T, T], [F, T, E, E, F, E, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_849 (And.intro z_1113 trivial))

theorem z_1115 : le (tf [F, T, E, E, E, E, F, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, E, T, F, T, E] [([F, E, T, E, E, E, F, E, E, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E]), ([F, T, E, E, E, E, F, E, E, E, E, T, F, E, T], [F, T, E, E, E, F, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_850 (And.intro z_1114 trivial))

theorem z_1116 : le (tf [F, T, E, E, E, E, F, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, T, E, E, T, F] [([F, E, T, E, E, E, F, E, E, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, E, E, T, E, E, T, F]), ([F, T, E, E, E, E, F, E, E, E, E, T, E, T, F], [F, T, E, E, E, E, F, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_851 (And.intro z_1115 trivial))

theorem z_1117 : le (tf [E, T, F, E, E, E, F, E, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, E, T, E, T, E, F] [([E, E, F, T, E, E, F, E, E, E, T, E, T, E, F], [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F]), ([E, T, F, E, E, E, F, E, E, E, E, T, T, E, F], [E, T, F, E, E, F, E, E, E, E, E, T, T, E, F]), ([E, T, F, E, E, E, F, E, E, E, T, E, E, T, F], [F, T, E, E, E, E, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1101 (And.intro z_1112 (And.intro z_1116 trivial)))

theorem z_1118 : le (tf [F, T, E, E, E, E, E, F, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, T, E, E, E, T, F] [([F, E, T, E, E, E, E, F, E, T, E, E, E, T, F], [F, E, T, E, E, E, F, E, E, T, E, E, E, T, F]), ([F, T, E, E, E, E, E, F, E, E, T, E, E, T, F], [F, T, E, E, E, E, F, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_852 (And.intro z_1116 trivial))

theorem z_1119 : le (tf [E, T, F, E, E, E, E, F, E, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, E, T, E, E, T, E, F] [([E, E, F, T, E, E, E, F, E, T, E, E, T, E, F], [E, F, E, T, E, E, E, F, E, T, E, E, T, E, F]), ([E, T, F, E, E, E, E, F, E, E, T, E, T, E, F], [E, T, F, E, E, E, F, E, E, E, T, E, T, E, F]), ([E, T, F, E, E, E, E, F, E, T, E, E, E, T, F], [F, T, E, E, E, E, E, F, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1102 (And.intro z_1117 (And.intro z_1118 trivial)))

theorem z_1120 : le (tf [E, F, E, T, E, E, F, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, T, E, E, E, E, E, T, F] [([E, F, E, E, T, E, F, T, E, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F]), ([E, F, E, T, E, E, F, E, T, E, E, E, E, T, F], [F, E, E, T, E, E, F, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_496 (And.intro z_524 trivial))

theorem z_1121 : le (tf [E, T, F, E, E, E, F, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, T, E, E, E, E, E, T, F] [([E, E, F, T, E, E, F, T, E, E, E, E, E, T, F], [E, F, E, T, E, E, F, T, E, E, E, E, E, T, F]), ([E, T, F, E, E, E, F, E, T, E, E, E, E, T, F], [E, T, F, E, E, F, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1120 (And.intro z_1066 trivial))

theorem z_1122 : le (tf [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F] [([E, E, F, T, E, E, E, T, F, E, E, E, T, E, F], [E, F, E, T, E, E, E, T, F, E, E, E, T, E, F]), ([E, T, F, E, E, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, E, E, F, E, T, E, E, T, E, F]), ([E, T, F, E, E, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, E, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1103 (And.intro z_1119 (And.intro z_1121 trivial)))

theorem z_1123 : le (tf [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F] [([E, E, F, T, E, E, E, T, E, F, E, T, E, E, F], [E, F, E, T, E, E, E, T, E, F, E, T, E, E, F]), ([E, T, F, E, E, E, E, E, T, F, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F]), ([E, T, F, E, E, E, E, T, E, F, E, E, T, E, F], [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_538 (And.intro z_1068 (And.intro z_1122 trivial)))

theorem z_1124 : le (tf [E, F, E, T, E, E, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, F, E, E, T, E, F] [([E, F, E, E, T, E, T, E, E, F, E, E, T, E, F], [F, E, E, E, T, E, T, E, E, F, E, E, T, E, F]), ([E, F, E, T, E, E, E, T, E, F, E, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F]), ([E, F, E, T, E, E, T, E, E, F, E, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_791 (And.intro z_537 (And.intro z_962 trivial)))

theorem z_1125 : le (tf [E, F, E, T, E, E, T, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, F, E, E, E, E, T, F] [([E, F, E, E, T, E, T, E, F, E, E, E, E, T, F], [F, E, E, E, T, E, T, E, F, E, E, E, E, T, F]), ([E, F, E, T, E, E, E, T, F, E, E, E, E, T, F], [F, E, E, T, E, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_790 (And.intro z_536 trivial))

theorem z_1126 : le (tf [E, T, F, E, E, E, T, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, F, E, E, E, E, T, F] [([E, E, F, T, E, E, T, E, F, E, E, E, E, T, F], [E, F, E, T, E, E, T, E, F, E, E, E, E, T, F]), ([E, T, F, E, E, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, E, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1125 (And.intro z_1121 trivial))

theorem z_1127 : le (tf [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F] [([E, E, F, T, E, E, T, E, E, F, E, E, T, E, F], [E, F, E, T, E, E, T, E, E, F, E, E, T, E, F]), ([E, T, F, E, E, E, E, T, E, F, E, E, T, E, F], [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F]), ([E, T, F, E, E, E, T, E, E, F, E, E, E, T, F], [E, T, F, E, E, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1124 (And.intro z_1122 (And.intro z_1126 trivial)))

theorem z_1128 : le (tf [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F] [([E, E, F, T, E, E, T, E, E, E, F, T, E, E, F], [E, F, E, T, E, E, T, E, E, E, F, T, E, E, F]), ([E, T, F, E, E, E, E, T, E, E, F, T, E, E, F], [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F]), ([E, T, F, E, E, E, T, E, E, E, F, E, T, E, F], [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1100 (And.intro z_1123 (And.intro z_1127 trivial)))

theorem z_1129 : le (tf [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F] [([E, E, F, T, E, E, T, E, E, E, T, E, F, E, F], [E, F, E, T, E, E, T, E, E, E, T, E, F, E, F]), ([E, T, F, E, E, E, E, T, E, E, T, E, F, E, F], [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F]), ([E, T, F, E, E, E, T, E, E, E, E, T, F, E, F], [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1098 (And.intro z_1092 (And.intro z_1128 trivial)))

theorem z_1130 : le (tf [E, T, F, E, E, E, T, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, T, E, E, E, F, F] [([E, E, F, T, E, E, T, E, E, T, E, E, E, F, F], [E, F, E, T, E, E, T, E, E, T, E, E, E, F, F]), ([E, T, F, E, E, E, E, T, E, T, E, E, E, F, F], [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F]), ([E, T, F, E, E, E, T, E, E, E, T, E, E, F, F], [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1099 (And.intro z_1093 (And.intro z_1129 trivial)))

theorem z_1131 : le (tf [E, T, E, F, E, E, T, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, T, E, E, E, E, F, F] [([E, E, T, F, E, E, T, E, T, E, E, E, E, F, F], [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F]), ([E, T, E, F, E, E, E, T, T, E, E, E, E, F, F], [E, T, F, E, E, E, E, T, T, E, E, E, E, F, F]), ([E, T, E, F, E, E, T, E, E, T, E, E, E, F, F], [E, T, F, E, E, E, T, E, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_957 (And.intro z_1094 (And.intro z_1130 trivial)))

theorem z_1132 : le (tf [E, T, E, E, F, E, T, T, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, T, E, E, E, E, E, F, F] [([E, E, T, E, F, E, T, T, E, E, E, E, E, F, F], [E, E, T, E, F, E, T, T, E, E, E, E, F, E, F]), ([E, T, E, E, F, E, T, E, T, E, E, E, E, F, F], [E, T, E, F, E, E, T, E, T, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_958 (And.intro z_1131 trivial))

theorem z_1133 : le (tf [E, T, E, F, E, E, E, T, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, T, E, E, E, F, E, F] [([E, E, T, F, E, E, E, T, T, E, E, E, F, E, F], [E, E, T, F, E, E, E, T, T, E, E, F, E, E, F]), ([E, T, E, F, E, E, E, T, E, T, E, E, F, E, F], [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_858 (And.intro z_1093 trivial))

theorem z_1134 : le (tf [E, T, E, F, E, E, T, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, E, T, E, E, F, E, F] [([E, E, T, F, E, E, T, E, E, T, E, E, F, E, F], [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F]), ([E, T, E, F, E, E, E, T, E, T, E, E, F, E, F], [E, T, F, E, E, E, E, T, E, T, E, E, F, E, F]), ([E, T, E, F, E, E, T, E, E, E, T, E, F, E, F], [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_956 (And.intro z_1093 (And.intro z_1129 trivial)))

theorem z_1135 : le (tf [E, T, E, E, F, E, T, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, E, T, E, E, E, F, E, F] [([E, E, T, E, F, E, T, E, T, E, E, E, F, E, F], [E, E, T, F, E, E, T, E, T, E, E, E, F, E, F]), ([E, T, E, E, F, E, E, T, T, E, E, E, F, E, F], [E, T, E, F, E, E, E, T, T, E, E, E, F, E, F]), ([E, T, E, E, F, E, T, E, E, T, E, E, F, E, F], [E, T, E, F, E, E, T, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_957 (And.intro z_1133 (And.intro z_1134 trivial)))

theorem z_1136 : le (tf [E, T, E, F, E, E, E, T, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, E, T, E, F, E, E, F] [([E, E, T, F, E, E, E, T, E, T, E, F, E, E, F], [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F]), ([E, T, E, F, E, E, E, E, T, T, E, F, E, E, F], [E, T, F, E, E, E, E, E, T, T, E, F, E, E, F]), ([E, T, E, F, E, E, E, T, E, E, T, F, E, E, F], [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_857 (And.intro z_1070 (And.intro z_1092 trivial)))

theorem z_1137 : le (tf [E, F, E, T, E, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, E, E, F, T, E, F] [([E, F, E, E, T, E, T, E, E, E, E, F, T, E, F], [F, E, E, E, T, E, T, E, E, E, E, F, T, E, F]), ([E, F, E, T, E, E, E, T, E, E, E, F, T, E, F], [F, E, E, T, E, E, E, T, E, E, E, F, T, E, F]), ([E, F, E, T, E, E, T, E, E, E, E, F, E, T, F], [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_860 (And.intro z_1033 (And.intro z_1096 trivial)))

theorem z_1138 : le (tf [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F] [([F, E, T, E, E, E, T, E, E, E, E, F, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F]), ([F, T, E, E, E, E, E, T, E, E, E, F, E, T, F], [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_964 (And.intro z_1090 trivial))

theorem z_1139 : le (tf [E, T, F, E, E, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, E, E, F, T, E, F] [([E, E, F, T, E, E, T, E, E, E, E, F, T, E, F], [E, F, E, T, E, E, T, E, E, E, E, F, T, E, F]), ([E, T, F, E, E, E, E, T, E, E, E, F, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F]), ([E, T, F, E, E, E, T, E, E, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1137 (And.intro z_1091 (And.intro z_1138 trivial)))

theorem z_1140 : le (tf [E, T, E, F, E, E, T, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, E, E, T, F, E, E, F] [([E, E, T, F, E, E, T, E, E, E, T, F, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F]), ([E, T, E, F, E, E, E, T, E, E, T, F, E, E, F], [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F]), ([E, T, E, F, E, E, T, E, E, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_955 (And.intro z_1092 (And.intro z_1139 trivial)))

theorem z_1141 : le (tf [E, T, E, E, F, E, T, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, E, E, T, E, F, E, E, F] [([E, E, T, E, F, E, T, E, E, T, E, F, E, E, F], [E, E, T, F, E, E, T, E, E, T, E, F, E, E, F]), ([E, T, E, E, F, E, E, T, E, T, E, F, E, E, F], [E, T, E, F, E, E, E, T, E, T, E, F, E, E, F]), ([E, T, E, E, F, E, T, E, E, E, T, F, E, E, F], [E, T, E, F, E, E, T, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_956 (And.intro z_1136 (And.intro z_1140 trivial)))

theorem z_1142 : le (tf [E, F, E, E, E, T, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, T, E, E, E, F] [([E, F, E, E, E, T, E, F, T, E, T, E, E, E, F], [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F]), ([E, F, E, E, E, T, T, F, E, E, E, T, E, E, F], [F, E, E, E, E, T, T, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 (And.intro z_749 trivial))

theorem z_1143 : le (tf [E, E, F, E, T, E, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, T, E, E, E, F] [([E, E, F, E, E, T, T, F, E, E, T, E, E, E, F], [E, F, E, E, E, T, T, F, E, E, T, E, E, E, F]), ([E, E, F, E, T, E, E, F, T, E, T, E, E, E, F], [E, F, E, E, T, E, E, F, T, E, T, E, E, E, F]), ([E, E, F, E, T, E, T, F, E, E, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1142 (And.intro z_739 (And.intro z_758 trivial)))

theorem z_1144 : le (tf [F, E, E, E, T, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, F, E, E, E, T, E, F] [([F, E, E, E, T, E, T, E, F, E, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F]), ([F, E, E, E, T, T, E, E, F, E, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_757 (And.intro z_973 trivial))

theorem z_1145 : le (tf [E, F, E, E, T, T, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, E, E, T, E, E, F] [([E, F, E, E, T, E, T, E, F, E, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F]), ([E, F, E, E, T, T, E, E, F, E, E, E, T, E, F], [F, E, E, E, T, T, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_758 (And.intro z_1144 trivial))

theorem z_1146 : le (tf [E, E, F, E, T, T, E, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, F, E, T, E, E, E, F] [([E, E, F, E, T, E, T, E, F, E, T, E, E, E, F], [E, E, F, E, T, E, T, F, E, E, T, E, E, E, F]), ([E, E, F, E, T, T, E, E, F, E, E, T, E, E, F], [E, F, E, E, T, T, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1143 (And.intro z_1145 trivial))

theorem z_1147 : le (tf [F, E, E, E, E, E, F, T, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, T, E, T, E, E, E, F] [([F, E, E, E, E, E, F, T, E, T, T, E, E, E, F], [F, E, E, E, E, F, E, T, E, T, T, E, E, E, F]), ([F, E, E, E, E, E, F, T, T, E, E, T, E, E, F], [F, E, E, E, E, F, E, T, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_352 (And.intro z_412 trivial))

theorem z_1148 : le (tf [E, F, E, E, E, T, F, E, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, T, E, T, E, E, E, F] [([E, F, E, E, E, E, F, T, T, E, T, E, E, E, F], [F, E, E, E, E, E, F, T, T, E, T, E, E, E, F]), ([E, F, E, E, E, T, F, E, E, T, T, E, E, E, F], [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F]), ([E, F, E, E, E, T, F, E, T, E, E, T, E, E, F], [F, E, E, E, E, T, F, E, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1147 (And.intro z_410 (And.intro z_420 trivial)))

theorem z_1149 : le (tf [E, F, E, E, T, E, F, E, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, T, T, E, E, E, F] [([E, F, E, E, E, T, F, E, E, T, T, E, E, E, F], [F, E, E, E, E, T, F, E, E, T, T, E, E, E, F]), ([E, F, E, E, T, E, F, E, E, T, E, T, E, E, F], [F, E, E, E, T, E, F, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_410 (And.intro z_479 trivial))

theorem z_1150 : le (tf [E, E, F, E, T, E, F, E, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, E, T, E, T, E, E, E, F] [([E, E, F, E, E, T, F, E, T, E, T, E, E, E, F], [E, F, E, E, E, T, F, E, T, E, T, E, E, E, F]), ([E, E, F, E, T, E, F, E, E, T, T, E, E, E, F], [E, F, E, E, T, E, F, E, E, T, T, E, E, E, F]), ([E, E, F, E, T, E, F, E, T, E, E, T, E, E, F], [E, F, E, E, T, E, F, E, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1148 (And.intro z_1149 (And.intro z_872 trivial)))

theorem z_1151 : le (tf [E, F, E, E, E, F, T, E, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, E, T, T, E, E, E, F] [([E, F, E, E, E, F, E, T, E, T, T, E, E, E, F], [F, E, E, E, E, F, E, T, E, T, T, E, E, E, F]), ([E, F, E, E, E, F, T, E, E, T, E, T, E, E, F], [F, E, E, E, E, F, T, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_352 (And.intro z_265 trivial))

theorem z_1152 : le (tf [E, E, F, E, T, F, E, E, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, E, T, T, E, E, E, F] [([E, E, F, E, E, F, T, E, E, T, T, E, E, E, F], [E, F, E, E, E, F, T, E, E, T, T, E, E, E, F]), ([E, E, F, E, T, F, E, E, E, T, E, T, E, E, F], [E, F, E, E, T, F, E, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1151 (And.intro z_880 trivial))

theorem z_1153 : le (tf [E, E, T, F, E, F, E, E, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, E, T, T, E, E, E, F] [([E, E, E, F, T, F, E, E, E, T, T, E, E, E, F], [E, E, F, E, T, F, E, E, E, T, T, E, E, E, F]), ([E, E, T, F, E, F, E, E, E, T, E, T, E, E, F], [E, E, T, F, F, E, E, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1152 (And.intro z_911 trivial))

theorem z_1154 : le (tf [E, E, T, F, E, E, F, E, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, E, T, E, T, E, E, E, F] [([E, E, E, F, T, E, F, E, T, E, T, E, E, E, F], [E, E, F, E, T, E, F, E, T, E, T, E, E, E, F]), ([E, E, T, F, E, E, F, E, E, T, T, E, E, E, F], [E, E, T, F, E, F, E, E, E, T, T, E, E, E, F]), ([E, E, T, F, E, E, F, E, T, E, E, T, E, E, F], [E, E, T, F, E, F, E, E, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1150 (And.intro z_1153 (And.intro z_924 trivial)))

theorem z_1155 : le (tf [E, F, E, E, E, T, T, F, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, E, T, E, F, E] [([E, F, E, E, E, T, E, F, T, E, E, T, E, F, E], [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E]), ([E, F, E, E, E, T, T, F, E, E, E, E, T, F, E], [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_821 (And.intro z_748 trivial))

theorem z_1156 : le (tf [F, E, E, E, T, E, E, F, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, T, E, F, E] [([F, E, E, E, E, T, E, F, E, T, E, T, E, F, E], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([F, E, E, E, T, E, E, F, E, E, T, T, E, F, E], [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]), ([F, E, E, E, T, E, E, F, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_474 (And.intro z_478 trivial)))

theorem z_1157 : le (tf [E, F, E, E, T, E, E, F, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, E, T, E, F, E] [([E, F, E, E, E, T, E, F, T, E, E, T, E, F, E], [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E]), ([E, F, E, E, T, E, E, F, E, T, E, T, E, F, E], [F, E, E, E, T, E, E, F, E, T, E, T, E, F, E]), ([E, F, E, E, T, E, E, F, T, E, E, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_821 (And.intro z_1156 (And.intro z_823 trivial)))

theorem z_1158 : le (tf [F, E, E, E, T, E, T, F, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, T, F, E, E, E, E, E, F, T] [([F, E, E, E, E, T, T, F, E, E, E, E, E, F, T], [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T]), ([F, E, E, E, T, E, E, F, T, E, E, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_747 (And.intro z_822 trivial))

theorem z_1159 : le (tf [E, F, E, E, T, E, T, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, E, T, F, E] [([E, F, E, E, E, T, T, F, E, E, E, E, T, F, E], [F, E, E, E, E, T, T, F, E, E, E, E, T, F, E]), ([E, F, E, E, T, E, E, F, T, E, E, E, T, F, E], [F, E, E, E, T, E, E, F, T, E, E, E, T, F, E]), ([E, F, E, E, T, E, T, F, E, E, E, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_748 (And.intro z_823 (And.intro z_1158 trivial)))

theorem z_1160 : le (tf [E, E, F, E, T, E, T, F, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, E, T, E, F, E] [([E, E, F, E, E, T, T, F, E, E, E, T, E, F, E], [E, F, E, E, E, T, T, F, E, E, E, T, E, F, E]), ([E, E, F, E, T, E, E, F, T, E, E, T, E, F, E], [E, F, E, E, T, E, E, F, T, E, E, T, E, F, E]), ([E, E, F, E, T, E, T, F, E, E, E, E, T, F, E], [E, F, E, E, T, E, T, F, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1155 (And.intro z_1157 (And.intro z_1159 trivial)))

theorem z_1161 : le (tf [F, E, E, E, E, E, F, T, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, T, E, E, T, E, F, E] [([F, E, E, E, E, E, F, T, E, T, E, T, E, F, E], [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E]), ([F, E, E, E, E, E, F, T, T, E, E, E, T, F, E], [F, E, E, E, E, F, E, T, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_353 (And.intro z_413 trivial))

theorem z_1162 : le (tf [E, F, E, E, E, T, F, E, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, T, E, E, T, E, F, E] [([E, F, E, E, E, E, F, T, T, E, E, T, E, F, E], [F, E, E, E, E, E, F, T, T, E, E, T, E, F, E]), ([E, F, E, E, E, T, F, E, E, T, E, T, E, F, E], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([E, F, E, E, E, T, F, E, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1161 (And.intro z_409 (And.intro z_419 trivial)))

theorem z_1163 : le (tf [E, F, E, E, T, E, F, E, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, T, E, T, E, F, E] [([E, F, E, E, E, T, F, E, E, T, E, T, E, F, E], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E]), ([E, F, E, E, T, E, F, E, E, E, T, T, E, F, E], [F, E, E, E, T, E, F, E, E, E, T, T, E, F, E]), ([E, F, E, E, T, E, F, E, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_474 (And.intro z_478 trivial)))

theorem z_1164 : le (tf [E, F, E, E, T, E, F, E, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, T, E, E, E, T, F, E] [([E, F, E, E, E, T, F, E, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([E, F, E, E, T, E, F, E, E, T, E, E, T, F, E], [F, E, E, E, T, E, F, E, E, T, E, E, T, F, E]), ([E, F, E, E, T, E, F, E, T, E, E, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_478 (And.intro z_822 trivial)))

theorem z_1165 : le (tf [E, E, F, E, T, E, F, E, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, E, T, E, E, T, E, F, E] [([E, E, F, E, E, T, F, E, T, E, E, T, E, F, E], [E, F, E, E, E, T, F, E, T, E, E, T, E, F, E]), ([E, E, F, E, T, E, F, E, E, T, E, T, E, F, E], [E, F, E, E, T, E, F, E, E, T, E, T, E, F, E]), ([E, E, F, E, T, E, F, E, T, E, E, E, T, F, E], [E, F, E, E, T, E, F, E, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1162 (And.intro z_1163 (And.intro z_1164 trivial)))

theorem z_1166 : le (tf [E, F, E, E, E, F, T, E, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, E, T, E, T, E, F, E] [([E, F, E, E, E, F, E, T, E, T, E, T, E, F, E], [F, E, E, E, E, F, E, T, E, T, E, T, E, F, E]), ([E, F, E, E, E, F, T, E, E, E, T, T, E, F, E], [F, E, E, E, E, F, T, E, E, E, T, T, E, F, E]), ([E, F, E, E, E, F, T, E, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_353 (And.intro z_264 (And.intro z_147 trivial)))

theorem z_1167 : le (tf [E, E, F, E, T, F, E, E, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, E, T, E, T, E, F, E] [([E, E, F, E, E, F, T, E, E, T, E, T, E, F, E], [E, F, E, E, E, F, T, E, E, T, E, T, E, F, E]), ([E, E, F, E, T, F, E, E, E, E, T, T, E, F, E], [E, F, E, E, T, F, E, E, E, E, T, T, E, F, E]), ([E, E, F, E, T, F, E, E, E, T, E, E, T, F, E], [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1166 (And.intro z_878 (And.intro z_879 trivial)))

theorem z_1168 : le (tf [E, E, T, F, E, F, E, E, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, E, T, E, T, E, F, E] [([E, E, E, F, T, F, E, E, E, T, E, T, E, F, E], [E, E, F, E, T, F, E, E, E, T, E, T, E, F, E]), ([E, E, T, F, E, F, E, E, E, E, T, T, E, F, E], [E, E, T, F, F, E, E, E, E, E, T, T, E, F, E]), ([E, E, T, F, E, F, E, E, E, T, E, E, T, F, E], [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1167 (And.intro z_905 (And.intro z_910 trivial)))

theorem z_1169 : le (tf [E, F, E, E, E, F, T, E, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, T, E, E, E, T, F, E] [([E, F, E, E, E, F, E, T, T, E, E, E, T, F, E], [F, E, E, E, E, F, E, T, T, E, E, E, T, F, E]), ([E, F, E, E, E, F, T, E, E, T, E, E, T, F, E], [F, E, E, E, E, F, T, E, E, T, E, E, T, F, E]), ([E, F, E, E, E, F, T, E, T, E, E, E, E, F, T], [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_147 (And.intro z_149 trivial)))

theorem z_1170 : le (tf [E, F, E, E, T, F, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, E, E, E, E, F, T] [([E, F, E, E, E, F, T, E, T, E, E, E, E, F, T], [F, E, E, E, E, F, T, E, T, E, E, E, E, F, T]), ([E, F, E, E, T, F, E, E, E, T, E, E, E, F, T], [F, E, E, E, T, F, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 (And.intro z_477 trivial))

theorem z_1171 : le (tf [E, E, F, E, T, F, E, E, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, T, E, E, E, T, F, E] [([E, E, F, E, E, F, T, E, T, E, E, E, T, F, E], [E, F, E, E, E, F, T, E, T, E, E, E, T, F, E]), ([E, E, F, E, T, F, E, E, E, T, E, E, T, F, E], [E, F, E, E, T, F, E, E, E, T, E, E, T, F, E]), ([E, E, F, E, T, F, E, E, T, E, E, E, E, F, T], [E, F, E, E, T, F, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1169 (And.intro z_879 (And.intro z_1170 trivial)))

theorem z_1172 : le (tf [F, E, E, T, E, F, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, T, E, E, E, E, F, T] [([F, E, E, E, T, F, E, E, T, E, E, E, E, F, T], [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T]), ([F, E, E, T, E, F, E, E, E, T, E, E, E, F, T], [F, E, E, T, F, E, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_752 (And.intro z_907 trivial))

theorem z_1173 : le (tf [E, F, T, E, E, F, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, T, E, E, E, E, F, T] [([E, F, E, T, E, F, E, E, T, E, E, E, E, F, T], [F, E, E, T, E, F, E, E, T, E, E, E, E, F, T]), ([E, F, T, E, E, F, E, E, E, T, E, E, E, F, T], [F, E, T, E, E, F, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1172 (And.intro z_1049 trivial))

theorem z_1174 : le (tf [E, E, T, F, E, F, E, E, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, T, E, E, E, T, F, E] [([E, E, E, F, T, F, E, E, T, E, E, E, T, F, E], [E, E, F, E, T, F, E, E, T, E, E, E, T, F, E]), ([E, E, T, F, E, F, E, E, E, T, E, E, T, F, E], [E, E, T, F, F, E, E, E, E, T, E, E, T, F, E]), ([E, E, T, F, E, F, E, E, T, E, E, E, E, F, T], [E, F, T, E, E, F, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1171 (And.intro z_910 (And.intro z_1173 trivial)))

theorem z_1175 : le (tf [E, E, T, F, E, E, F, E, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, E, T, E, E, T, E, F, E] [([E, E, E, F, T, E, F, E, T, E, E, T, E, F, E], [E, E, F, E, T, E, F, E, T, E, E, T, E, F, E]), ([E, E, T, F, E, E, F, E, E, T, E, T, E, F, E], [E, E, T, F, E, F, E, E, E, T, E, T, E, F, E]), ([E, E, T, F, E, E, F, E, T, E, E, E, T, F, E], [E, E, T, F, E, F, E, E, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1165 (And.intro z_1168 (And.intro z_1174 trivial)))

theorem z_1176 : le (tf [F, E, E, E, F, E, E, T, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, T, E, E, F, T, E, E] [([F, E, E, E, F, E, E, T, E, T, E, F, T, E, E], [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E]), ([F, E, E, E, F, E, E, T, T, E, E, F, E, T, E], [F, E, E, F, E, E, E, T, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_912 trivial))

theorem z_1177 : le (tf [F, E, E, E, E, F, T, E, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, E, F, T, E, E] [([F, E, E, E, E, F, E, T, T, E, E, F, T, E, E], [F, E, E, E, F, E, E, T, T, E, E, F, T, E, E]), ([F, E, E, E, E, F, T, E, E, T, E, F, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E]), ([F, E, E, E, E, F, T, E, T, E, E, F, E, T, E], [F, E, E, E, F, E, T, E, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1176 (And.intro z_342 (And.intro z_913 trivial)))

theorem z_1178 : le (tf [F, E, E, E, E, T, E, F, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, F, T, E, E] [([F, E, E, E, E, E, T, F, T, E, E, F, T, E, E], [F, E, E, E, E, F, T, E, T, E, E, F, T, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, F, T, E, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]), ([F, E, E, E, E, T, E, F, T, E, E, F, E, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1177 (And.intro z_408 (And.intro z_429 trivial)))

theorem z_1179 : le (tf [E, F, E, E, E, T, T, F, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, E, F, T, E, E] [([E, F, E, E, E, T, E, F, T, E, E, F, T, E, E], [F, E, E, E, E, T, E, F, T, E, E, F, T, E, E]), ([E, F, E, E, E, T, T, F, E, E, E, F, E, T, E], [F, E, E, E, E, T, T, F, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1178 (And.intro z_751 trivial))

theorem z_1180 : le (tf [F, E, E, E, T, E, E, F, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, F, T, E, E] [([F, E, E, E, E, T, E, F, E, T, E, F, T, E, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]), ([F, E, E, E, T, E, E, F, E, E, T, F, T, E, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]), ([F, E, E, E, T, E, E, F, E, T, E, F, E, T, E], [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_408 (And.intro z_473 (And.intro z_634 trivial)))

theorem z_1181 : le (tf [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E] [([F, E, E, E, E, T, E, F, T, E, E, F, E, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]), ([F, E, E, E, T, E, E, F, E, T, E, F, E, T, E], [F, E, E, E, T, E, E, F, E, T, F, E, E, T, E]), ([F, E, E, E, T, E, E, F, T, E, E, F, E, E, T], [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_634 (And.intro z_754 trivial)))

theorem z_1182 : le (tf [E, F, E, E, T, E, E, F, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, E, F, T, E, E] [([E, F, E, E, E, T, E, F, T, E, E, F, T, E, E], [F, E, E, E, E, T, E, F, T, E, E, F, T, E, E]), ([E, F, E, E, T, E, E, F, E, T, E, F, T, E, E], [F, E, E, E, T, E, E, F, E, T, E, F, T, E, E]), ([E, F, E, E, T, E, E, F, T, E, E, F, E, T, E], [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1178 (And.intro z_1180 (And.intro z_1181 trivial)))

theorem z_1183 : le (tf [E, F, E, E, T, E, T, F, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, F, E, T, E] [([E, F, E, E, E, T, T, F, E, E, E, F, E, T, E], [F, E, E, E, E, T, T, F, E, E, E, F, E, T, E]), ([E, F, E, E, T, E, E, F, T, E, E, F, E, T, E], [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E]), ([E, F, E, E, T, E, T, F, E, E, E, F, E, E, T], [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_751 (And.intro z_1181 (And.intro z_755 trivial)))

theorem z_1184 : le (tf [E, E, F, E, T, E, T, F, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, E, F, T, E, E] [([E, E, F, E, E, T, T, F, E, E, E, F, T, E, E], [E, F, E, E, E, T, T, F, E, E, E, F, T, E, E]), ([E, E, F, E, T, E, E, F, T, E, E, F, T, E, E], [E, F, E, E, T, E, E, F, T, E, E, F, T, E, E]), ([E, E, F, E, T, E, T, F, E, E, E, F, E, T, E], [E, F, E, E, T, E, T, F, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1179 (And.intro z_1182 (And.intro z_1183 trivial)))

theorem z_1185 : le (tf [F, E, E, E, T, E, F, E, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, T, E, F, E, T, E] [([F, E, E, E, E, T, F, E, E, T, E, F, E, T, E], [F, E, E, E, E, T, F, E, E, T, F, E, E, T, E]), ([F, E, E, E, T, E, F, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]), ([F, E, E, E, T, E, F, E, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_407 (And.intro z_472 (And.intro z_480 trivial)))

theorem z_1186 : le (tf [E, F, E, E, T, E, F, E, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, T, E, F, T, E, E] [([E, F, E, E, E, T, F, E, E, T, E, F, T, E, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E]), ([E, F, E, E, T, E, F, E, E, E, T, F, T, E, E], [F, E, E, E, T, E, F, E, E, E, T, F, T, E, E]), ([E, F, E, E, T, E, F, E, E, T, E, F, E, T, E], [F, E, E, E, T, E, F, E, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_408 (And.intro z_473 (And.intro z_1185 trivial)))

theorem z_1187 : le (tf [E, F, E, E, T, E, F, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, T, E, E, F, E, T, E] [([E, F, E, E, E, T, F, E, T, E, E, F, E, T, E], [F, E, E, E, E, T, F, E, T, E, E, F, E, T, E]), ([E, F, E, E, T, E, F, E, E, T, E, F, E, T, E], [F, E, E, E, T, E, F, E, E, T, E, F, E, T, E]), ([E, F, E, E, T, E, F, E, T, E, E, F, E, E, T], [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_1185 (And.intro z_754 trivial)))

theorem z_1188 : le (tf [E, E, F, E, T, E, F, E, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, E, T, E, E, F, T, E, E] [([E, E, F, E, E, T, F, E, T, E, E, F, T, E, E], [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E]), ([E, E, F, E, T, E, F, E, E, T, E, F, T, E, E], [E, F, E, E, T, E, F, E, E, T, E, F, T, E, E]), ([E, E, F, E, T, E, F, E, T, E, E, F, E, T, E], [E, F, E, E, T, E, F, E, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_653 (And.intro z_1186 (And.intro z_1187 trivial)))

theorem z_1189 : le (tf [E, F, E, E, E, F, T, E, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, E, T, E, F, T, E, E] [([E, F, E, E, E, F, E, T, E, T, E, F, T, E, E], [F, E, E, E, E, F, E, T, E, T, E, F, T, E, E]), ([E, F, E, E, E, F, T, E, E, E, T, F, T, E, E], [F, E, E, E, E, F, T, E, E, E, T, F, T, E, E]), ([E, F, E, E, E, F, T, E, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_356 (And.intro z_143 (And.intro z_282 trivial)))

theorem z_1190 : le (tf [E, F, E, E, T, F, E, E, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, T, E, F, E, T, E] [([E, F, E, E, E, F, T, E, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([E, F, E, E, T, F, E, E, E, E, T, F, E, T, E], [F, E, E, E, T, F, E, E, E, E, T, F, E, T, E]), ([E, F, E, E, T, F, E, E, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_472 (And.intro z_480 trivial)))

theorem z_1191 : le (tf [E, E, F, E, T, F, E, E, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, E, T, E, F, T, E, E] [([E, E, F, E, E, F, T, E, E, T, E, F, T, E, E], [E, F, E, E, E, F, T, E, E, T, E, F, T, E, E]), ([E, E, F, E, T, F, E, E, E, E, T, F, T, E, E], [E, F, E, E, T, F, E, E, E, E, T, F, T, E, E]), ([E, E, F, E, T, F, E, E, E, T, E, F, E, T, E], [E, F, E, E, T, F, E, E, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1189 (And.intro z_877 (And.intro z_1190 trivial)))

theorem z_1192 : le (tf [F, E, T, E, E, F, E, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, T, E, F, E, E, T] [([F, E, E, T, E, F, E, E, E, T, E, F, E, E, T], [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T]), ([F, E, T, E, E, F, E, E, E, E, T, F, E, E, T], [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_916 (And.intro z_902 trivial))

theorem z_1193 : le (tf [E, F, T, E, E, F, E, E, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, E, T, E, F, E, T, E] [([E, F, E, T, E, F, E, E, E, T, E, F, E, T, E], [E, F, E, T, F, E, E, E, E, T, E, F, E, T, E]), ([E, F, T, E, E, F, E, E, E, E, T, F, E, T, E], [E, F, T, E, F, E, E, E, E, E, T, F, E, T, E]), ([E, F, T, E, E, F, E, E, E, T, E, F, E, E, T], [F, E, T, E, E, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_917 (And.intro z_903 (And.intro z_1192 trivial)))

theorem z_1194 : le (tf [E, E, T, F, E, F, E, E, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, E, T, E, F, T, E, E] [([E, E, E, F, T, F, E, E, E, T, E, F, T, E, E], [E, E, F, E, T, F, E, E, E, T, E, F, T, E, E]), ([E, E, T, F, E, F, E, E, E, E, T, F, T, E, E], [E, E, T, F, F, E, E, E, E, E, T, F, T, E, E]), ([E, E, T, F, E, F, E, E, E, T, E, F, E, T, E], [E, F, T, E, E, F, E, E, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1191 (And.intro z_904 (And.intro z_1193 trivial)))

theorem z_1195 : le (tf [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T] [([F, E, E, E, E, F, E, T, T, E, E, F, E, E, T], [F, E, E, E, F, E, E, T, T, E, E, F, E, E, T]), ([F, E, E, E, E, F, T, E, E, T, E, F, E, E, T], [F, E, E, E, F, E, T, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_424 (And.intro z_281 trivial))

theorem z_1196 : le (tf [E, F, E, E, E, F, T, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, T, E, E, F, E, T, E] [([E, F, E, E, E, F, E, T, T, E, E, F, E, T, E], [F, E, E, E, E, F, E, T, T, E, E, F, E, T, E]), ([E, F, E, E, E, F, T, E, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([E, F, E, E, E, F, T, E, T, E, E, F, E, E, T], [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_425 (And.intro z_282 (And.intro z_1195 trivial)))

theorem z_1197 : le (tf [E, F, E, E, T, F, E, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, T, E, E, F, E, E, T] [([E, F, E, E, E, F, T, E, T, E, E, F, E, E, T], [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T]), ([E, F, E, E, T, F, E, E, E, T, E, F, E, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1195 (And.intro z_480 trivial))

theorem z_1198 : le (tf [E, E, F, E, T, F, E, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, T, E, E, F, E, T, E] [([E, E, F, E, E, F, T, E, T, E, E, F, E, T, E], [E, F, E, E, E, F, T, E, T, E, E, F, E, T, E]), ([E, E, F, E, T, F, E, E, E, T, E, F, E, T, E], [E, F, E, E, T, F, E, E, E, T, E, F, E, T, E]), ([E, E, F, E, T, F, E, E, T, E, E, F, E, E, T], [E, F, E, E, T, F, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1196 (And.intro z_1190 (And.intro z_1197 trivial)))

theorem z_1199 : le (tf [E, F, E, T, F, E, E, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, T, E, E, F, E, E, T] [([E, F, E, E, F, T, E, E, T, E, E, F, E, E, T], [F, E, E, E, F, T, E, E, T, E, E, F, E, E, T]), ([E, F, E, T, F, E, E, E, E, T, E, F, E, E, T], [F, E, E, T, F, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_428 (And.intro z_916 trivial))

theorem z_1200 : le (tf [E, F, T, E, E, F, E, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, T, E, E, F, E, E, T] [([E, F, E, T, E, F, E, E, T, E, E, F, E, E, T], [E, F, E, T, F, E, E, E, T, E, E, F, E, E, T]), ([E, F, T, E, E, F, E, E, E, T, E, F, E, E, T], [F, E, T, E, E, F, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1199 (And.intro z_1192 trivial))

theorem z_1201 : le (tf [E, E, T, F, E, F, E, E, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, T, E, E, F, E, T, E] [([E, E, E, F, T, F, E, E, T, E, E, F, E, T, E], [E, E, F, E, T, F, E, E, T, E, E, F, E, T, E]), ([E, E, T, F, E, F, E, E, E, T, E, F, E, T, E], [E, F, T, E, E, F, E, E, E, T, E, F, E, T, E]), ([E, E, T, F, E, F, E, E, T, E, E, F, E, E, T], [E, F, T, E, E, F, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1198 (And.intro z_1193 (And.intro z_1200 trivial)))

theorem z_1202 : le (tf [E, E, T, F, E, E, F, E, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, E, T, E, E, F, T, E, E] [([E, E, E, F, T, E, F, E, T, E, E, F, T, E, E], [E, E, F, E, T, E, F, E, T, E, E, F, T, E, E]), ([E, E, T, F, E, E, F, E, E, T, E, F, T, E, E], [E, E, T, F, E, F, E, E, E, T, E, F, T, E, E]), ([E, E, T, F, E, E, F, E, T, E, E, F, E, T, E], [E, E, T, F, E, F, E, E, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1188 (And.intro z_1194 (And.intro z_1201 trivial)))

theorem z_1203 : le (tf [E, F, E, E, T, F, T, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, T, E, E, E, E, F, E, E, T] [([E, F, E, E, T, F, E, T, E, E, E, F, E, E, T], [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_722 trivial)

theorem z_1204 : le (tf [E, E, F, E, T, F, T, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, T, E, E, E, E, F, E, T, E] [([E, E, F, E, T, F, E, T, E, E, E, F, E, T, E], [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E]), ([E, E, F, E, T, F, T, E, E, E, E, F, E, E, T], [E, F, E, E, T, F, T, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_723 (And.intro z_1203 trivial))

theorem z_1205 : le (tf [F, E, T, E, F, E, E, E, E, F, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, F, E, E, T, T, E] [([F, E, E, T, F, E, E, E, E, F, E, E, T, T, E], [F, E, E, T, F, E, E, E, F, E, E, E, T, T, E]), ([F, E, T, E, F, E, E, E, E, F, E, E, T, E, T], [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_893 (And.intro z_1060 trivial))

theorem z_1206 : le (tf [F, E, T, E, F, E, E, E, E, F, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, E, F, E, T, E, E, T] [([F, E, E, T, F, E, E, E, E, F, E, T, E, E, T], [F, E, E, T, F, E, E, E, F, E, E, T, E, E, T]), ([F, E, T, E, F, E, E, E, E, F, E, E, T, E, T], [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_894 (And.intro z_1060 trivial))

theorem z_1207 : le (tf [F, E, T, E, E, F, E, E, E, F, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, F, E, T, E, T, E] [([F, E, E, T, E, F, E, E, E, F, E, T, E, T, E], [F, E, E, T, F, E, E, E, E, F, E, T, E, T, E]), ([F, E, T, E, E, F, E, E, E, F, E, E, T, T, E], [F, E, T, E, F, E, E, E, E, F, E, E, T, T, E]), ([F, E, T, E, E, F, E, E, E, F, E, T, E, E, T], [F, E, T, E, F, E, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_895 (And.intro z_1205 (And.intro z_1206 trivial)))

theorem z_1208 : le (tf [F, E, T, E, E, F, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, F, T, E, E, E, T] [([F, E, E, T, E, F, E, E, E, F, T, E, E, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T]), ([F, E, T, E, E, F, E, E, E, F, E, T, E, E, T], [F, E, T, E, F, E, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_896 (And.intro z_1206 trivial))

theorem z_1209 : le (tf [E, F, T, E, E, F, E, E, E, F, T, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, E, F, T, E, E, T, E] [([E, F, E, T, E, F, E, E, E, F, T, E, E, T, E], [E, F, E, T, F, E, E, E, E, F, T, E, E, T, E]), ([E, F, T, E, E, F, E, E, E, F, E, T, E, T, E], [F, E, T, E, E, F, E, E, E, F, E, T, E, T, E]), ([E, F, T, E, E, F, E, E, E, F, T, E, E, E, T], [F, E, T, E, E, F, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_897 (And.intro z_1207 (And.intro z_1208 trivial)))

theorem z_1210 : le (tf [E, F, T, E, F, E, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, F, E, E, E, E, F, T, E, E, E, T] [([E, F, E, T, F, E, E, E, E, F, T, E, E, E, T], [F, E, E, T, F, E, E, E, E, F, T, E, E, E, T]), ([E, F, T, E, F, E, E, E, E, F, E, T, E, E, T], [F, E, T, E, F, E, E, E, E, F, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_896 (And.intro z_1206 trivial))

theorem z_1211 : le (tf [E, E, T, F, F, E, E, E, T, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, E, T, F, E, E, E, E, T] [([E, E, T, F, F, E, E, E, E, F, T, E, E, E, T], [E, F, T, E, F, E, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1210 trivial)

theorem z_1212 : le (tf [E, E, T, F, E, F, E, E, T, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, T, F, E, E, E, T, E] [([E, E, E, F, T, F, E, E, T, F, E, E, E, T, E], [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E]), ([E, E, T, F, E, F, E, E, E, F, T, E, E, T, E], [E, F, T, E, E, F, E, E, E, F, T, E, E, T, E]), ([E, E, T, F, E, F, E, E, T, F, E, E, E, E, T], [E, E, T, F, F, E, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_716 (And.intro z_1209 (And.intro z_1211 trivial)))

theorem z_1213 : le (tf [E, E, T, F, F, E, E, T, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, E, T, E, E, F, E, E, E, T] [([E, E, T, F, F, E, E, E, T, E, F, E, E, E, T], [E, E, T, F, F, E, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1211 trivial)

theorem z_1214 : le (tf [E, E, T, F, E, F, E, T, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, T, E, E, F, E, E, T, E] [([E, E, E, F, T, F, E, T, E, E, F, E, E, T, E], [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E]), ([E, E, T, F, E, F, E, E, T, E, F, E, E, T, E], [E, E, T, F, E, F, E, E, T, F, E, E, E, T, E]), ([E, E, T, F, E, F, E, T, E, E, F, E, E, E, T], [E, E, T, F, F, E, E, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_723 (And.intro z_1212 (And.intro z_1213 trivial)))

theorem z_1215 : le (tf [E, E, T, F, F, E, T, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, F, E, T, E, E, E, E, F, E, E, T] [([E, E, T, F, F, E, E, T, E, E, E, F, E, E, T], [E, E, T, F, F, E, E, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1213 trivial)

theorem z_1216 : le (tf [E, E, T, F, E, F, T, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, T, E, E, E, E, F, E, T, E] [([E, E, E, F, T, F, T, E, E, E, E, F, E, T, E], [E, E, F, E, T, F, T, E, E, E, E, F, E, T, E]), ([E, E, T, F, E, F, E, T, E, E, E, F, E, T, E], [E, E, T, F, E, F, E, T, E, E, F, E, E, T, E]), ([E, E, T, F, E, F, T, E, E, E, E, F, E, E, T], [E, E, T, F, F, E, T, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1204 (And.intro z_1214 (And.intro z_1215 trivial)))

theorem z_1217 : le (tf [E, E, T, F, E, E, T, F, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, E, F, T, E, E] [([E, E, E, F, T, E, T, F, E, E, E, F, T, E, E], [E, E, F, E, T, E, T, F, E, E, E, F, T, E, E]), ([E, E, T, F, E, E, E, F, T, E, E, F, T, E, E], [E, E, T, F, E, E, F, E, T, E, E, F, T, E, E]), ([E, E, T, F, E, E, T, F, E, E, E, F, E, T, E], [E, E, T, F, E, F, T, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1184 (And.intro z_1202 (And.intro z_1216 trivial)))

theorem z_1218 : le (tf [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E] [([E, E, E, F, T, E, T, F, E, E, E, T, E, F, E], [E, E, F, E, T, E, T, F, E, E, E, T, E, F, E]), ([E, E, T, F, E, E, E, F, T, E, E, T, E, F, E], [E, E, T, F, E, E, F, E, T, E, E, T, E, F, E]), ([E, E, T, F, E, E, T, F, E, E, E, E, T, F, E], [E, E, T, F, E, E, T, F, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1160 (And.intro z_1175 (And.intro z_1217 trivial)))

theorem z_1219 : le (tf [E, E, T, F, E, E, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, T, E, E, E, F] [([E, E, E, F, T, E, T, F, E, E, T, E, E, E, F], [E, E, F, E, T, E, T, F, E, E, T, E, E, E, F]), ([E, E, T, F, E, E, E, F, T, E, T, E, E, E, F], [E, E, T, F, E, E, F, E, T, E, T, E, E, E, F]), ([E, E, T, F, E, E, T, F, E, E, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1143 (And.intro z_1154 (And.intro z_1218 trivial)))

theorem z_1220 : le (tf [E, F, E, E, T, T, E, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, F, E, E, E, E, T, E, F] [([E, F, E, E, T, E, T, F, E, E, E, E, T, E, F], [F, E, E, E, T, E, T, F, E, E, E, E, T, E, F]), ([E, F, E, E, T, T, E, F, E, E, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_757 (And.intro z_973 trivial))

theorem z_1221 : le (tf [E, E, F, E, T, T, E, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, F, E, E, E, T, E, E, F] [([E, E, F, E, T, E, T, F, E, E, E, T, E, E, F], [E, F, E, E, T, E, T, F, E, E, E, T, E, E, F]), ([E, E, F, E, T, T, E, F, E, E, E, E, T, E, F], [E, F, E, E, T, T, E, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_758 (And.intro z_1220 trivial))

theorem z_1222 : le (tf [E, F, E, E, T, T, F, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, E, E, E, T, F] [([E, F, E, E, T, E, F, T, E, E, E, E, E, T, F], [F, E, E, E, T, E, F, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_496 trivial)

theorem z_1223 : le (tf [E, E, F, E, T, T, F, E, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, E, E, E, T, E, F] [([E, E, F, E, T, E, F, T, E, E, E, E, T, E, F], [E, F, E, E, T, E, F, T, E, E, E, E, T, E, F]), ([E, E, F, E, T, T, F, E, E, E, E, E, E, T, F], [E, F, E, E, T, T, F, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_873 (And.intro z_1222 trivial))

theorem z_1224 : le (tf [F, E, E, E, T, E, F, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, T, E, E, E, E, F, E, T] [([F, E, E, E, E, T, F, T, E, E, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T]), ([F, E, E, E, T, E, F, E, T, E, E, E, F, E, T], [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_752 trivial))

theorem z_1225 : le (tf [E, F, E, E, T, E, F, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, E, E, E, F, T, E] [([E, F, E, E, E, T, F, T, E, E, E, E, F, T, E], [F, E, E, E, E, T, F, T, E, E, E, E, F, T, E]), ([E, F, E, E, T, E, F, E, T, E, E, E, F, T, E], [F, E, E, E, T, E, F, E, T, E, E, E, F, T, E]), ([E, F, E, E, T, E, F, T, E, E, E, E, F, E, T], [F, E, E, E, T, E, F, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 (And.intro z_753 (And.intro z_1224 trivial)))

theorem z_1226 : le (tf [E, F, E, E, T, T, F, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, E, E, F, E, T] [([E, F, E, E, T, E, F, T, E, E, E, E, F, E, T], [F, E, E, E, T, E, F, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1224 trivial)

theorem z_1227 : le (tf [E, E, F, E, T, T, F, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, E, E, E, F, T, E] [([E, E, F, E, T, E, F, T, E, E, E, E, F, T, E], [E, F, E, E, T, E, F, T, E, E, E, E, F, T, E]), ([E, E, F, E, T, T, F, E, E, E, E, E, F, E, T], [E, F, E, E, T, T, F, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1225 (And.intro z_1226 trivial))

theorem z_1228 : le (tf [F, E, E, E, E, F, T, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, T, E, E, E, E, F, E, T] [([F, E, E, E, E, F, T, E, T, E, E, E, F, E, T], [F, E, E, E, F, E, T, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 trivial)

theorem z_1229 : le (tf [E, F, E, E, E, F, T, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, T, E, E, E, E, F, T, E] [([E, F, E, E, E, F, T, E, T, E, E, E, F, T, E], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E]), ([E, F, E, E, E, F, T, T, E, E, E, E, F, E, T], [F, E, E, E, E, F, T, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_1228 trivial))

theorem z_1230 : le (tf [E, F, E, E, T, F, E, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, T, E, E, E, E, F, E, T] [([E, F, E, E, E, F, T, T, E, E, E, E, F, E, T], [F, E, E, E, E, F, T, T, E, E, E, E, F, E, T]), ([E, F, E, E, T, F, E, E, T, E, E, E, F, E, T], [F, E, E, E, T, F, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1228 (And.intro z_752 trivial))

theorem z_1231 : le (tf [E, E, F, E, T, F, E, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, T, E, E, E, E, F, T, E] [([E, E, F, E, E, F, T, T, E, E, E, E, F, T, E], [E, F, E, E, E, F, T, T, E, E, E, E, F, T, E]), ([E, E, F, E, T, F, E, E, T, E, E, E, F, T, E], [E, E, F, E, T, F, E, E, T, E, E, F, E, T, E]), ([E, E, F, E, T, F, E, T, E, E, E, E, F, E, T], [E, F, E, E, T, F, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1229 (And.intro z_1198 (And.intro z_1230 trivial)))

theorem z_1232 : le (tf [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T] [([E, F, E, E, F, T, E, T, E, E, E, E, F, E, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T]), ([E, F, E, T, F, E, E, E, T, E, E, E, F, E, T], [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_918 trivial))

theorem z_1233 : le (tf [E, F, T, E, E, F, E, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, T, E, E, E, E, F, E, T] [([E, F, E, T, E, F, E, T, E, E, E, E, F, E, T], [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T]), ([E, F, T, E, E, F, E, E, T, E, E, E, F, E, T], [E, F, T, E, E, F, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1232 (And.intro z_1200 trivial))

theorem z_1234 : le (tf [E, E, T, F, E, F, E, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, T, E, E, E, E, F, T, E] [([E, E, E, F, T, F, E, T, E, E, E, E, F, T, E], [E, E, F, E, T, F, E, T, E, E, E, E, F, T, E]), ([E, E, T, F, E, F, E, E, T, E, E, E, F, T, E], [E, E, T, F, E, F, E, E, T, E, E, F, E, T, E]), ([E, E, T, F, E, F, E, T, E, E, E, E, F, E, T], [E, F, T, E, E, F, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1231 (And.intro z_1201 (And.intro z_1233 trivial)))

theorem z_1235 : le (tf [E, F, E, E, T, T, F, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, F, E, E, E, F, E, E, E, T] [([E, F, E, E, T, E, F, T, E, E, F, E, E, E, T], [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_722 trivial)

theorem z_1236 : le (tf [E, F, E, T, E, T, F, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, E, E, E, E, F, E, E, T] [([E, F, E, E, T, T, F, E, E, E, E, F, E, E, T], [E, F, E, E, T, T, F, E, E, E, F, E, E, E, T]), ([E, F, E, T, E, E, F, T, E, E, E, F, E, E, T], [E, F, E, T, E, E, F, T, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1235 (And.intro z_724 trivial))

theorem z_1237 : le (tf [E, F, T, E, E, T, F, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, F, E, E, E, E, E, F, E, T] [([E, F, E, T, E, T, F, E, E, E, E, E, F, E, T], [E, F, E, T, E, T, F, E, E, E, E, F, E, E, T]), ([E, F, T, E, E, E, F, T, E, E, E, E, F, E, T], [E, F, T, E, E, F, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1236 (And.intro z_1233 trivial))

theorem z_1238 : le (tf [E, E, T, F, E, T, F, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, E, E, F, T, E] [([E, E, E, F, T, T, F, E, E, E, E, E, F, T, E], [E, E, F, E, T, T, F, E, E, E, E, E, F, T, E]), ([E, E, T, F, E, E, F, T, E, E, E, E, F, T, E], [E, E, T, F, E, F, E, T, E, E, E, E, F, T, E]), ([E, E, T, F, E, T, F, E, E, E, E, E, F, E, T], [E, F, T, E, E, T, F, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1227 (And.intro z_1234 (And.intro z_1237 trivial)))

theorem z_1239 : le (tf [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F] [([E, E, E, F, T, T, F, E, E, E, E, E, T, E, F], [E, E, F, E, T, T, F, E, E, E, E, E, T, E, F]), ([E, E, T, F, E, E, F, T, E, E, E, E, T, E, F], [E, E, T, F, E, F, E, T, E, E, E, E, T, E, F]), ([E, E, T, F, E, T, F, E, E, E, E, E, E, T, F], [E, E, T, F, E, T, F, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1223 (And.intro z_933 (And.intro z_1238 trivial)))

theorem z_1240 : le (tf [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F] [([E, E, E, F, T, T, E, F, E, E, E, T, E, E, F], [E, E, F, E, T, T, E, F, E, E, E, T, E, E, F]), ([E, E, T, F, E, E, T, F, E, E, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E]), ([E, E, T, F, E, T, E, F, E, E, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1221 (And.intro z_1218 (And.intro z_1239 trivial)))

theorem z_1241 : le (tf [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F] [([E, E, E, F, T, T, E, E, F, E, T, E, E, E, F], [E, E, F, E, T, T, E, E, F, E, T, E, E, E, F]), ([E, E, T, F, E, E, T, E, F, E, T, E, E, E, F], [E, E, T, F, E, E, T, F, E, E, T, E, E, E, F]), ([E, E, T, F, E, T, E, E, F, E, E, T, E, E, F], [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1146 (And.intro z_1219 (And.intro z_1240 trivial)))

theorem z_1242 : le (tf [E, E, T, F, T, E, F, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, F, E, E, E, E, E, E, T, F] [([E, E, T, F, E, T, F, E, E, E, E, E, E, T, F], [E, E, T, F, E, T, F, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1238 trivial)

theorem z_1243 : le (tf [E, E, T, F, T, E, E, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, F, E, E, E, E, T, E, F] [([E, E, T, F, E, T, E, F, E, E, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F]), ([E, E, T, F, T, E, E, F, E, E, E, E, E, T, F], [E, E, T, F, T, E, F, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1239 (And.intro z_1242 trivial))

theorem z_1244 : le (tf [E, E, T, F, T, E, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, E, F, E, E, T, E, E, F] [([E, E, T, F, E, T, E, E, F, E, E, T, E, E, F], [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F]), ([E, E, T, F, T, E, E, E, F, E, E, E, T, E, F], [E, E, T, F, T, E, E, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1240 (And.intro z_1243 trivial))

theorem z_1245 : le (tf [E, E, T, F, T, E, E, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, E, E, E, F, T, E, E, E, F] [([E, E, T, F, E, T, E, E, E, F, T, E, E, E, F], [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F]), ([E, E, T, F, T, E, E, E, E, F, E, T, E, E, F], [E, E, T, F, T, E, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1241 (And.intro z_1244 trivial))

theorem z_1246 : le (tf [E, T, E, F, E, E, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, E, F, T, E, E, E, F] [([E, E, T, F, E, E, E, T, E, F, T, E, E, E, F], [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F]), ([E, T, E, F, E, E, E, E, T, F, T, E, E, E, F], [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F]), ([E, T, E, F, E, E, E, T, E, F, E, T, E, E, F], [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_935 (And.intro z_1069 (And.intro z_1123 trivial)))

theorem z_1247 : le (tf [E, T, E, F, E, E, T, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, E, F, E, T, E, E, F] [([E, E, T, F, E, E, T, E, E, F, E, T, E, E, F], [E, E, T, F, E, E, T, E, F, E, E, T, E, E, F]), ([E, T, E, F, E, E, E, T, E, F, E, T, E, E, F], [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F]), ([E, T, E, F, E, E, T, E, E, F, E, E, T, E, F], [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_954 (And.intro z_1123 (And.intro z_1127 trivial)))

theorem z_1248 : le (tf [E, T, E, E, F, E, T, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, E, E, F, T, E, E, E, F] [([E, E, T, E, F, E, T, E, E, F, T, E, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F]), ([E, T, E, E, F, E, E, T, E, F, T, E, E, E, F], [E, T, E, F, E, E, E, T, E, F, T, E, E, E, F]), ([E, T, E, E, F, E, T, E, E, F, E, T, E, E, F], [E, T, E, F, E, E, T, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_955 (And.intro z_1246 (And.intro z_1247 trivial)))

theorem z_1249 : le (tf [E, F, E, E, F, T, T, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, T, E, E, E, E, E, E, T, F] [([E, F, E, E, F, T, E, T, E, E, E, E, E, T, F], [E, F, E, E, F, T, E, T, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 trivial)

theorem z_1250 : le (tf [E, E, F, T, F, E, T, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, F, T, F, E, T, E, E, E, E, E, E, T, F] [([E, E, F, E, F, T, T, E, E, E, E, E, E, T, F], [E, F, E, E, F, T, T, E, E, E, E, E, E, T, F]), ([E, E, F, T, F, E, E, T, E, E, E, E, E, T, F], [E, F, E, T, F, E, E, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1249 (And.intro z_931 trivial))

theorem z_1251 : le (tf [F, E, T, F, E, E, E, E, E, E, F, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, E, F, E, T, T, E] [([F, E, E, F, T, E, E, E, E, E, F, E, T, T, E], [F, E, E, F, T, E, E, E, E, F, E, E, T, T, E]), ([F, E, T, F, E, E, E, E, E, E, F, E, T, E, T], [F, E, T, F, E, E, E, E, E, F, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_695 (And.intro z_1060 trivial))

theorem z_1252 : le (tf [F, T, F, E, E, E, E, E, E, E, F, E, E, T, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, E, E, E, E, E, F, E, E, T, T] [([F, E, F, T, E, E, E, E, E, E, F, E, E, T, T], [F, F, E, T, E, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_518 trivial)

theorem z_1253 : le (tf [F, T, F, E, E, E, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, T, F, E, E, E, E, E, E, E, E, F, T, E, T] [([F, E, F, T, E, E, E, E, E, E, E, F, T, E, T], [F, E, F, T, E, E, E, E, E, E, F, E, T, E, T]), ([F, T, F, E, E, E, E, E, E, E, E, F, E, T, T], [F, T, F, E, E, E, E, E, E, E, F, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_519 (And.intro z_1252 trivial))

theorem z_1254 : le (tf [F, T, E, F, E, E, E, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, T, E, F, E, E, E, E, E, E, E, F, T, T, E] [([F, E, T, F, E, E, E, E, E, E, E, F, T, T, E], [F, E, T, F, E, E, E, E, E, E, F, E, T, T, E]), ([F, T, E, F, E, E, E, E, E, E, E, F, T, E, T], [F, T, F, E, E, E, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1251 (And.intro z_1253 trivial))

theorem z_1255 : le (tf [E, T, F, F, E, E, F, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, F, E, E, E, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1256 : le (tf [E, T, F, F, E, E, E, F, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, F, E, E, E, E, T, E, T] [([E, T, F, F, E, E, E, F, E, E, E, E, E, T, T], [E, T, F, F, E, E, F, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1255 trivial)

theorem z_1257 : le (tf [E, T, F, F, E, E, E, E, F, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, F, E, E, T, E, E, T] [([E, T, F, F, E, E, E, E, F, E, E, E, T, E, T], [E, T, F, F, E, E, E, F, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1256 trivial)

theorem z_1258 : le (tf [E, T, F, F, E, E, E, E, E, F, T, E, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, F, T, E, E, E, T] [([E, T, F, F, E, E, E, E, E, F, E, T, E, E, T], [E, T, F, F, E, E, E, E, F, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1257 trivial)

theorem z_1259 : le (tf [E, T, F, F, E, E, E, E, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, E, T, F, E, T, E] [([E, T, F, F, E, E, E, E, E, E, E, F, T, T, E], [F, T, E, F, E, E, E, E, E, E, E, F, T, T, E]), ([E, T, F, F, E, E, E, E, E, E, T, F, E, E, T], [E, T, F, F, E, E, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1254 (And.intro z_1258 trivial))

theorem z_1260 : le (tf [E, T, F, F, E, E, E, E, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, T, E, F, E, E, T] [([E, T, F, F, E, E, E, E, E, E, T, F, E, E, T], [E, T, F, F, E, E, E, E, E, F, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1258 trivial)

theorem z_1261 : le (tf [E, T, F, F, E, E, E, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, E, T, E, E, F, T, E] [([E, T, F, F, E, E, E, E, E, E, T, E, F, T, E], [E, T, F, F, E, E, E, E, E, E, T, F, E, T, E]), ([E, T, F, F, E, E, E, E, E, T, E, E, F, E, T], [E, T, F, F, E, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1259 (And.intro z_1260 trivial))

theorem z_1262 : le (tf [E, T, F, F, E, E, E, E, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, T, E, E, E, E, T, F] [([E, T, F, F, E, E, E, E, E, T, E, E, E, T, F], [E, T, F, F, E, E, E, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1261 trivial)

theorem z_1263 : le (tf [E, T, F, E, F, E, E, T, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, T, E, E, E, E, E, T, F] [([E, E, F, T, F, E, E, T, E, E, E, E, E, T, F], [E, F, E, T, F, E, E, T, E, E, E, E, E, T, F]), ([E, T, F, E, F, E, E, E, T, E, E, E, E, T, F], [E, T, F, F, E, E, E, E, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_931 (And.intro z_1262 trivial))

theorem z_1264 : le (tf [E, T, F, E, E, F, T, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, T, E, E, E, E, E, E, T, F] [([E, E, F, T, E, F, T, E, E, E, E, E, E, T, F], [E, E, F, T, F, E, T, E, E, E, E, E, E, T, F]), ([E, T, F, E, E, F, E, T, E, E, E, E, E, T, F], [E, T, F, E, F, E, E, T, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1250 (And.intro z_1263 trivial))

theorem z_1265 : le (tf [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F] [([E, E, F, T, E, E, T, F, E, E, E, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, E, E, T, E, F]), ([E, T, F, E, E, E, E, F, T, E, E, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, E, E, T, E, F]), ([E, T, F, E, E, E, T, F, E, E, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_760 (And.intro z_1067 (And.intro z_1264 trivial)))

theorem z_1266 : le (tf [E, T, E, F, E, E, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, F, E, E, E, T, E, E, F] [([E, E, T, F, E, E, T, F, E, E, E, T, E, E, F], [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E]), ([E, T, E, F, E, E, E, F, T, E, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F]), ([E, T, E, F, E, E, T, F, E, E, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1218 (And.intro z_1068 (And.intro z_1265 trivial)))

theorem z_1267 : le (tf [E, F, E, T, E, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, F, E, E, E, T, E, F] [([E, F, E, E, T, T, E, E, F, E, E, E, T, E, F], [F, E, E, E, T, T, E, E, F, E, E, E, T, E, F]), ([E, F, E, T, E, E, T, E, F, E, E, E, T, E, F], [E, F, E, T, E, E, T, F, E, E, E, E, T, E, F]), ([E, F, E, T, E, T, E, E, F, E, E, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1144 (And.intro z_760 (And.intro z_974 trivial)))

theorem z_1268 : le (tf [E, F, E, T, E, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, F, E, E, E, E, E, T, F] [([E, F, E, E, T, T, E, F, E, E, E, E, E, T, F], [F, E, E, E, T, T, E, F, E, E, E, E, E, T, F]), ([E, F, E, T, E, E, T, F, E, E, E, E, E, T, F], [F, E, E, T, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_973 (And.intro z_759 trivial))

theorem z_1269 : le (tf [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F] [([E, E, F, T, E, T, E, F, E, E, E, E, E, T, F], [E, F, E, T, E, T, E, F, E, E, E, E, E, T, F]), ([E, T, F, E, E, E, T, F, E, E, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1268 (And.intro z_1264 trivial))

theorem z_1270 : le (tf [E, T, F, E, E, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, F, E, E, E, T, E, F] [([E, E, F, T, E, T, E, E, F, E, E, E, T, E, F], [E, F, E, T, E, T, E, E, F, E, E, E, T, E, F]), ([E, T, F, E, E, E, T, E, F, E, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F]), ([E, T, F, E, E, T, E, E, F, E, E, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1267 (And.intro z_1265 (And.intro z_1269 trivial)))

theorem z_1271 : le (tf [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F] [([E, E, T, F, E, T, E, E, F, E, E, T, E, E, F], [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F]), ([E, T, E, F, E, E, T, E, F, E, E, T, E, E, F], [E, T, E, F, E, E, T, F, E, E, E, T, E, E, F]), ([E, T, E, F, E, T, E, E, F, E, E, E, T, E, F], [E, T, F, E, E, T, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1240 (And.intro z_1266 (And.intro z_1270 trivial)))

theorem z_1272 : le (tf [E, F, E, T, T, E, E, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, F, E, E, T, E, F] [([E, F, E, T, E, T, E, E, E, F, E, E, T, E, F], [E, F, E, T, E, T, E, E, F, E, E, E, T, E, F]), ([E, F, E, T, T, E, E, E, E, F, E, E, E, T, F], [F, E, E, T, T, E, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1267 (And.intro z_978 trivial))

theorem z_1273 : le (tf [E, F, E, T, T, E, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, F, E, E, E, E, T, F] [([E, F, E, T, E, T, E, E, F, E, E, E, E, T, F], [F, E, E, T, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_974 trivial)

theorem z_1274 : le (tf [E, T, F, E, T, E, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, F, E, E, E, E, T, F] [([E, E, F, T, T, E, E, E, F, E, E, E, E, T, F], [E, F, E, T, T, E, E, E, F, E, E, E, E, T, F]), ([E, T, F, E, E, T, E, E, F, E, E, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1273 (And.intro z_1269 trivial))

theorem z_1275 : le (tf [E, T, F, E, T, E, E, E, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, F, E, E, T, E, F] [([E, E, F, T, T, E, E, E, E, F, E, E, T, E, F], [E, F, E, T, T, E, E, E, E, F, E, E, T, E, F]), ([E, T, F, E, E, T, E, E, E, F, E, E, T, E, F], [E, T, F, E, E, T, E, E, F, E, E, E, T, E, F]), ([E, T, F, E, T, E, E, E, E, F, E, E, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1272 (And.intro z_1270 (And.intro z_1274 trivial)))

theorem z_1276 : le (tf [E, T, E, F, T, E, E, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, T, E, E, E, E, F, E, T, E, E, F] [([E, E, T, F, T, E, E, E, E, F, E, T, E, E, F], [E, E, T, F, T, E, E, E, F, E, E, T, E, E, F]), ([E, T, E, F, E, T, E, E, E, F, E, T, E, E, F], [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F]), ([E, T, E, F, T, E, E, E, E, F, E, E, T, E, F], [E, T, F, E, T, E, E, E, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1244 (And.intro z_1271 (And.intro z_1275 trivial)))

theorem z_1277 : le (tf [E, T, E, E, T, F, E, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, E, F, T, E, E, E, F] [([E, E, T, E, T, F, E, E, E, F, T, E, E, E, F], [E, E, T, F, T, E, E, E, E, F, T, E, E, E, F]), ([E, T, E, E, E, F, T, E, E, F, T, E, E, E, F], [E, T, E, E, F, E, T, E, E, F, T, E, E, E, F]), ([E, T, E, E, T, F, E, E, E, F, E, T, E, E, F], [E, T, E, F, T, E, E, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1245 (And.intro z_1248 (And.intro z_1276 trivial)))

theorem z_1278 : le (tf [E, T, E, E, T, F, E, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, E, T, E, F, E, E, F] [([E, E, T, E, T, F, E, E, E, T, E, F, E, E, F], [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F]), ([E, T, E, E, E, F, T, E, E, T, E, F, E, E, F], [E, T, E, E, F, E, T, E, E, T, E, F, E, E, F]), ([E, T, E, E, T, F, E, E, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_982 (And.intro z_1141 (And.intro z_1277 trivial)))

theorem z_1279 : le (tf [E, T, E, E, T, F, E, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, T, E, E, E, F, E, F] [([E, E, T, E, T, F, E, E, T, E, E, E, F, E, F], [E, E, T, E, T, F, E, E, T, E, E, F, E, E, F]), ([E, T, E, E, E, F, T, E, T, E, E, E, F, E, F], [E, T, E, E, F, E, T, E, T, E, E, E, F, E, F]), ([E, T, E, E, T, F, E, E, E, T, E, E, F, E, F], [E, T, E, E, T, F, E, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_983 (And.intro z_1135 (And.intro z_1278 trivial)))

theorem z_1280 : le (tf [E, T, E, E, T, F, E, T, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, T, E, E, E, E, E, F, F] [([E, E, T, E, T, F, E, T, E, E, E, E, E, F, F], [E, E, T, E, T, F, E, T, E, E, E, E, F, E, F]), ([E, T, E, E, E, F, T, T, E, E, E, E, E, F, F], [E, T, E, E, F, E, T, T, E, E, E, E, E, F, F]), ([E, T, E, E, T, F, E, E, T, E, E, E, E, F, F], [E, T, E, E, T, F, E, E, T, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_984 (And.intro z_1132 (And.intro z_1279 trivial)))

theorem z_1281 : le (tf [E, T, E, E, T, T, F, E, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, T, F, E, E, E, E, E, E, F, F] [([E, E, T, E, T, T, F, E, E, E, E, E, E, F, F], [E, E, T, E, T, T, F, E, E, E, E, E, F, E, F]), ([E, T, E, E, T, E, F, T, E, E, E, E, E, F, F], [E, T, E, E, T, F, E, T, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_985 (And.intro z_1280 trivial))

theorem z_1282 : le (tf [F, E, E, E, E, E, T, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, T, F, E, E, E, E, F] [([F, E, E, E, E, E, T, T, E, F, T, E, E, E, F], [F, E, E, E, E, E, T, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 trivial)

theorem z_1283 : le (tf [E, F, E, E, E, T, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, T, F, E, E, E, E, F] [([E, F, E, E, E, E, T, T, T, F, E, E, E, E, F], [F, E, E, E, E, E, T, T, T, F, E, E, E, E, F]), ([E, F, E, E, E, T, E, T, E, F, T, E, E, E, F], [F, E, E, E, E, T, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1282 (And.intro z_435 trivial))

theorem z_1284 : le (tf [E, E, F, E, E, T, T, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, E, T, F, E, E, E, E, F] [([E, E, F, E, E, T, E, T, T, F, E, E, E, E, F], [E, F, E, E, E, T, E, T, T, F, E, E, E, E, F]), ([E, E, F, E, E, T, T, E, E, F, T, E, E, E, F], [E, E, F, E, E, T, T, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1283 (And.intro z_548 trivial))

theorem z_1285 : le (tf [E, E, E, F, E, T, T, T, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, T, E, F, E, E, E, E, F] [([E, E, E, F, E, T, T, E, T, F, E, E, E, E, F], [E, E, F, E, E, T, T, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1284 trivial)

theorem z_1286 : le (tf [F, E, E, E, E, E, T, F, T, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, T, E, E, E, E, F] [([F, E, E, E, E, E, T, F, T, E, T, E, E, E, F], [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_350 trivial)

theorem z_1287 : le (tf [E, F, E, E, E, T, E, F, T, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, T, E, E, E, E, F] [([E, F, E, E, E, E, T, F, T, T, E, E, E, E, F], [F, E, E, E, E, E, T, F, T, T, E, E, E, E, F]), ([E, F, E, E, E, T, E, F, T, E, T, E, E, E, F], [F, E, E, E, E, T, E, F, T, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1286 (And.intro z_421 trivial))

theorem z_1288 : le (tf [E, E, F, E, E, T, T, F, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, T, E, E, E, E, F] [([E, E, F, E, E, T, E, F, T, T, E, E, E, E, F], [E, F, E, E, E, T, E, F, T, T, E, E, E, E, F]), ([E, E, F, E, E, T, T, F, E, E, T, E, E, E, F], [E, F, E, E, E, T, T, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1287 (And.intro z_1142 trivial))

theorem z_1289 : le (tf [E, E, E, F, E, T, T, F, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, T, E, E, E, E, E, F] [([E, E, E, F, E, T, T, F, E, T, E, E, E, E, F], [E, E, F, E, E, T, T, F, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1288 trivial)

theorem z_1290 : le (tf [E, F, E, E, E, E, T, F, T, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, T, E, E, E, F, E] [([E, F, E, E, E, E, T, F, T, E, T, E, E, F, E], [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_350 trivial)

theorem z_1291 : le (tf [F, E, E, E, E, T, E, F, E, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, T, E, E, F, E] [([F, E, E, E, E, E, T, F, E, T, T, E, E, F, E], [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, T, E, F, E], [F, E, E, E, E, T, F, E, E, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_409 trivial))

theorem z_1292 : le (tf [E, F, E, E, E, T, E, F, T, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, E, T, E, E, F, E] [([E, F, E, E, E, E, T, F, T, E, T, E, E, F, E], [F, E, E, E, E, E, T, F, T, E, T, E, E, F, E]), ([E, F, E, E, E, T, E, F, E, T, T, E, E, F, E], [F, E, E, E, E, T, E, F, E, T, T, E, E, F, E]), ([E, F, E, E, E, T, E, F, T, E, E, T, E, F, E], [F, E, E, E, E, T, E, F, T, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_350 (And.intro z_1291 (And.intro z_821 trivial)))

theorem z_1293 : le (tf [E, E, F, E, E, T, E, F, T, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, T, T, E, E, E, F, E] [([E, E, F, E, E, E, T, F, T, T, E, E, E, F, E], [E, F, E, E, E, E, T, F, T, T, E, E, E, F, E]), ([E, E, F, E, E, T, E, F, T, E, T, E, E, F, E], [E, F, E, E, E, T, E, F, T, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1290 (And.intro z_1292 trivial))

theorem z_1294 : le (tf [E, E, F, E, E, T, T, F, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, E, T, E, E, F, E] [([E, E, F, E, E, T, E, F, T, E, T, E, E, F, E], [E, F, E, E, E, T, E, F, T, E, T, E, E, F, E]), ([E, E, F, E, E, T, T, F, E, E, E, T, E, F, E], [E, F, E, E, E, T, T, F, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1292 (And.intro z_1155 trivial))

theorem z_1295 : le (tf [E, E, E, F, E, T, T, F, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, T, E, E, E, F, E] [([E, E, E, F, E, T, E, F, T, T, E, E, E, F, E], [E, E, F, E, E, T, E, F, T, T, E, E, E, F, E]), ([E, E, E, F, E, T, T, F, E, E, T, E, E, F, E], [E, E, F, E, E, T, T, F, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1293 (And.intro z_1294 trivial))

theorem z_1296 : le (tf [E, F, E, E, E, E, T, F, T, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, E, T, E, F, E, E] [([E, F, E, E, E, E, T, F, E, T, T, E, F, E, E], [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]), ([E, F, E, E, E, E, T, F, T, E, E, T, F, E, E], [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_349 trivial))

theorem z_1297 : le (tf [E, E, F, E, E, E, T, F, T, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, F, T, T, E, E, F, E, E] [([E, E, F, E, E, E, T, F, T, E, T, E, F, E, E], [E, F, E, E, E, E, T, F, T, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1296 trivial)

theorem z_1298 : le (tf [E, F, E, E, E, T, E, F, E, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, E, T, T, E, F, E, E] [([E, F, E, E, E, E, T, F, E, T, T, E, F, E, E], [F, E, E, E, E, E, T, F, E, T, T, E, F, E, E]), ([E, F, E, E, E, T, E, F, E, T, E, T, F, E, E], [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_584 trivial))

theorem z_1299 : le (tf [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E] [([F, E, E, E, E, E, T, F, T, E, E, E, F, T, E], [F, E, E, E, E, F, T, E, T, E, E, E, F, T, E]), ([F, E, E, E, E, T, E, F, E, T, E, E, F, T, E], [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E]), ([F, E, E, E, E, T, E, F, T, E, E, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_583 (And.intro z_746 trivial)))

theorem z_1300 : le (tf [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E] [([E, F, E, E, E, E, T, F, T, E, E, T, F, E, E], [F, E, E, E, E, E, T, F, T, E, E, T, F, E, E]), ([E, F, E, E, E, T, E, F, E, T, E, T, F, E, E], [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E]), ([E, F, E, E, E, T, E, F, T, E, E, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_349 (And.intro z_584 (And.intro z_1299 trivial)))

theorem z_1301 : le (tf [E, E, F, E, E, T, E, F, T, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, T, E, T, E, F, E, E] [([E, E, F, E, E, E, T, F, T, E, T, E, F, E, E], [E, F, E, E, E, E, T, F, T, E, T, E, F, E, E]), ([E, E, F, E, E, T, E, F, E, T, T, E, F, E, E], [E, F, E, E, E, T, E, F, E, T, T, E, F, E, E]), ([E, E, F, E, E, T, E, F, T, E, E, T, F, E, E], [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1296 (And.intro z_1298 (And.intro z_1300 trivial)))

theorem z_1302 : le (tf [E, E, E, F, E, T, E, F, T, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, F, T, T, E, E, F, E, E] [([E, E, E, F, E, E, T, F, T, T, E, E, F, E, E], [E, E, F, E, E, E, T, F, T, T, E, E, F, E, E]), ([E, E, E, F, E, T, E, F, T, E, T, E, F, E, E], [E, E, F, E, E, T, E, F, T, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1297 (And.intro z_1301 trivial))

theorem z_1303 : le (tf [F, E, E, E, E, E, E, F, T, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, T, T, T, F, E, E, E] [([F, E, E, E, E, E, E, F, T, T, E, F, T, E, E], [F, E, E, E, E, E, F, E, T, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_278 trivial)

theorem z_1304 : le (tf [E, F, E, E, E, E, T, F, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, E, T, T, F, E, E, E] [([E, F, E, E, E, E, E, F, T, T, T, F, E, E, E], [F, E, E, E, E, E, E, F, T, T, T, F, E, E, E]), ([E, F, E, E, E, E, T, F, E, T, E, F, T, E, E], [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1303 (And.intro z_283 trivial))

theorem z_1305 : le (tf [E, F, E, E, E, E, T, F, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, E, E, F, T, E, E] [([E, F, E, E, E, E, T, F, E, T, E, F, T, E, E], [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E]), ([E, F, E, E, E, E, T, F, T, E, E, F, E, T, E], [E, F, E, E, E, F, T, E, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_283 (And.intro z_1196 trivial))

theorem z_1306 : le (tf [E, E, F, E, E, E, T, F, T, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, F, T, E, T, F, E, E, E] [([E, E, F, E, E, E, T, F, E, T, T, F, E, E, E], [E, F, E, E, E, E, T, F, E, T, T, F, E, E, E]), ([E, E, F, E, E, E, T, F, T, E, E, F, T, E, E], [E, F, E, E, E, E, T, F, T, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 (And.intro z_1305 trivial))

theorem z_1307 : le (tf [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E] [([F, E, E, E, E, E, T, F, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([F, E, E, E, E, T, E, F, E, E, T, F, E, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E]), ([F, E, E, E, E, T, E, F, E, T, E, F, E, E, T], [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_219 (And.intro z_616 trivial)))

theorem z_1308 : le (tf [E, F, E, E, E, T, E, F, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, E, T, E, F, T, E, E] [([E, F, E, E, E, E, T, F, E, T, E, F, T, E, E], [F, E, E, E, E, E, T, F, E, T, E, F, T, E, E]), ([E, F, E, E, E, T, E, F, E, E, T, F, T, E, E], [F, E, E, E, E, T, E, F, E, E, T, F, T, E, E]), ([E, F, E, E, E, T, E, F, E, T, E, F, E, T, E], [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_283 (And.intro z_220 (And.intro z_1307 trivial)))

theorem z_1309 : le (tf [E, E, F, E, E, T, E, F, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, E, T, T, F, E, E, E] [([E, E, F, E, E, E, T, F, E, T, T, F, E, E, E], [E, F, E, E, E, E, T, F, E, T, T, F, E, E, E]), ([E, E, F, E, E, T, E, F, E, T, E, F, T, E, E], [E, F, E, E, E, T, E, F, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 (And.intro z_1308 trivial))

theorem z_1310 : le (tf [F, E, E, E, E, T, E, F, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, T, E, E, F, E, E, T] [([F, E, E, E, E, E, T, F, T, E, E, F, E, E, T], [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T]), ([F, E, E, E, E, T, E, F, E, T, E, F, E, E, T], [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1195 (And.intro z_616 trivial))

theorem z_1311 : le (tf [E, F, E, E, E, T, E, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, T, E, E, F, E, T, E] [([E, F, E, E, E, E, T, F, T, E, E, F, E, T, E], [E, F, E, E, E, F, T, E, T, E, E, F, E, T, E]), ([E, F, E, E, E, T, E, F, E, T, E, F, E, T, E], [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E]), ([E, F, E, E, E, T, E, F, T, E, E, F, E, E, T], [F, E, E, E, E, T, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1196 (And.intro z_1307 (And.intro z_1310 trivial)))

theorem z_1312 : le (tf [E, E, F, E, E, T, E, F, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, T, E, E, F, T, E, E] [([E, E, F, E, E, E, T, F, T, E, E, F, T, E, E], [E, F, E, E, E, E, T, F, T, E, E, F, T, E, E]), ([E, E, F, E, E, T, E, F, E, T, E, F, T, E, E], [E, F, E, E, E, T, E, F, E, T, E, F, T, E, E]), ([E, E, F, E, E, T, E, F, T, E, E, F, E, T, E], [E, F, E, E, E, T, E, F, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1305 (And.intro z_1308 (And.intro z_1311 trivial)))

theorem z_1313 : le (tf [E, E, E, F, E, T, E, F, T, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, F, T, E, T, F, E, E, E] [([E, E, E, F, E, E, T, F, T, E, T, F, E, E, E], [E, E, F, E, E, E, T, F, T, E, T, F, E, E, E]), ([E, E, E, F, E, T, E, F, E, T, T, F, E, E, E], [E, E, F, E, E, T, E, F, E, T, T, F, E, E, E]), ([E, E, E, F, E, T, E, F, T, E, E, F, T, E, E], [E, E, F, E, E, T, E, F, T, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1306 (And.intro z_1309 (And.intro z_1312 trivial)))

theorem z_1314 : le (tf [F, E, E, F, E, E, E, E, T, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, T, T, T, F, E, E, E] [([F, E, E, F, E, E, E, E, T, T, E, F, T, E, E], [F, E, E, F, E, E, E, E, T, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 trivial)

theorem z_1315 : le (tf [F, E, E, E, F, E, E, T, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, T, E, T, T, F, E, E, E] [([F, E, E, E, F, E, E, E, T, T, T, F, E, E, E], [F, E, E, F, E, E, E, E, T, T, T, F, E, E, E]), ([F, E, E, E, F, E, E, T, E, T, E, F, T, E, E], [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1314 (And.intro z_333 trivial))

theorem z_1316 : le (tf [F, E, E, E, E, F, T, E, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, T, T, F, E, E, E] [([F, E, E, E, E, F, E, T, E, T, T, F, E, E, E], [F, E, E, E, F, E, E, T, E, T, T, F, E, E, E]), ([F, E, E, E, E, F, T, E, E, T, E, F, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1315 (And.intro z_342 trivial))

theorem z_1317 : le (tf [F, E, E, E, E, T, E, F, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, T, T, F, E, E, E] [([F, E, E, E, E, E, T, F, E, T, T, F, E, E, E], [F, E, E, E, E, F, T, E, E, T, T, F, E, E, E]), ([F, E, E, E, E, T, E, F, E, T, E, F, T, E, E], [F, E, E, E, E, T, F, E, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1316 (And.intro z_408 trivial))

theorem z_1318 : le (tf [E, F, E, E, T, E, E, F, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, E, T, T, F, E, E, E] [([E, F, E, E, E, T, E, F, E, T, T, F, E, E, E], [F, E, E, E, E, T, E, F, E, T, T, F, E, E, E]), ([E, F, E, E, T, E, E, F, E, T, E, F, T, E, E], [F, E, E, E, T, E, E, F, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1317 (And.intro z_1180 trivial))

theorem z_1319 : le (tf [F, E, E, T, E, E, E, F, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, E, T, E, F, E, T, E] [([F, E, E, E, T, E, E, F, E, T, E, F, E, T, E], [F, E, E, E, T, E, F, E, E, T, E, F, E, T, E]), ([F, E, E, T, E, E, E, F, E, E, T, F, E, T, E], [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E]), ([F, E, E, T, E, E, E, F, E, T, E, F, E, E, T], [F, E, E, T, E, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1185 (And.intro z_512 (And.intro z_643 trivial)))

theorem z_1320 : le (tf [E, F, E, T, E, E, E, F, E, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, T, E, F, T, E, E] [([E, F, E, E, T, E, E, F, E, T, E, F, T, E, E], [F, E, E, E, T, E, E, F, E, T, E, F, T, E, E]), ([E, F, E, T, E, E, E, F, E, E, T, F, T, E, E], [F, E, E, T, E, E, E, F, E, E, T, F, T, E, E]), ([E, F, E, T, E, E, E, F, E, T, E, F, E, T, E], [F, E, E, T, E, E, E, F, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1180 (And.intro z_513 (And.intro z_1319 trivial)))

theorem z_1321 : le (tf [E, E, F, T, E, E, E, F, E, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, F, E, T, T, F, E, E, E] [([E, E, F, E, T, E, E, F, E, T, T, F, E, E, E], [E, F, E, E, T, E, E, F, E, T, T, F, E, E, E]), ([E, E, F, T, E, E, E, F, E, T, E, F, T, E, E], [E, F, E, T, E, E, E, F, E, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1318 (And.intro z_1320 trivial))

theorem z_1322 : le (tf [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T] [([F, E, E, E, T, E, E, F, T, E, E, F, E, E, T], [F, E, E, E, T, E, F, E, T, E, E, F, E, E, T]), ([F, E, E, T, E, E, E, F, E, T, E, F, E, E, T], [F, E, E, T, E, E, E, F, E, T, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_754 (And.intro z_643 trivial))

theorem z_1323 : le (tf [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E] [([E, F, E, E, T, E, E, F, T, E, E, F, E, T, E], [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E]), ([E, F, E, T, E, E, E, F, E, T, E, F, E, T, E], [F, E, E, T, E, E, E, F, E, T, E, F, E, T, E]), ([E, F, E, T, E, E, E, F, T, E, E, F, E, E, T], [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1181 (And.intro z_1319 (And.intro z_1322 trivial)))

theorem z_1324 : le (tf [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E] [([E, E, F, E, T, E, E, F, T, E, E, F, T, E, E], [E, F, E, E, T, E, E, F, T, E, E, F, T, E, E]), ([E, E, F, T, E, E, E, F, E, T, E, F, T, E, E], [E, F, E, T, E, E, E, F, E, T, E, F, T, E, E]), ([E, E, F, T, E, E, E, F, T, E, E, F, E, T, E], [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1182 (And.intro z_1320 (And.intro z_1323 trivial)))

theorem z_1325 : le (tf [E, E, E, T, F, E, E, F, T, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, F, T, E, T, F, E, E, E] [([E, E, E, E, F, T, E, F, T, E, T, F, E, E, E], [E, E, E, F, E, T, E, F, T, E, T, F, E, E, E]), ([E, E, E, T, F, E, E, F, E, T, T, F, E, E, E], [E, E, F, T, E, E, E, F, E, T, T, F, E, E, E]), ([E, E, E, T, F, E, E, F, T, E, E, F, T, E, E], [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1313 (And.intro z_1321 (And.intro z_1324 trivial)))

theorem z_1326 : le (tf [E, E, E, T, F, E, E, F, T, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, F, T, T, E, E, F, E, E] [([E, E, E, E, F, T, E, F, T, T, E, E, F, E, E], [E, E, E, F, E, T, E, F, T, T, E, E, F, E, E]), ([E, E, E, T, F, E, E, F, T, E, T, E, F, E, E], [E, E, E, T, F, E, E, F, T, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1302 (And.intro z_1325 trivial))

theorem z_1327 : le (tf [E, F, E, E, E, T, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, E, E, F, T, E] [([E, F, E, E, E, T, E, F, T, E, E, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E]), ([E, F, E, E, E, T, T, F, E, E, E, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1299 (And.intro z_747 trivial))

theorem z_1328 : le (tf [E, E, F, E, E, T, T, F, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, E, E, T, F, E, E] [([E, E, F, E, E, T, E, F, T, E, E, T, F, E, E], [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E]), ([E, E, F, E, E, T, T, F, E, E, E, E, F, T, E], [E, F, E, E, E, T, T, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1300 (And.intro z_1327 trivial))

theorem z_1329 : le (tf [E, E, E, F, E, T, T, F, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, E, T, E, F, E, E] [([E, E, E, F, E, T, E, F, T, E, T, E, F, E, E], [E, E, F, E, E, T, E, F, T, E, T, E, F, E, E]), ([E, E, E, F, E, T, T, F, E, E, E, T, F, E, E], [E, E, F, E, E, T, T, F, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1301 (And.intro z_1328 trivial))

theorem z_1330 : le (tf [F, E, E, E, E, F, T, E, T, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, T, E, F, E, E, T, E] [([F, E, E, E, E, F, E, T, T, E, F, E, E, T, E], [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E]), ([F, E, E, E, E, F, T, E, E, T, F, E, E, T, E], [F, E, E, E, F, E, T, E, E, T, F, E, E, T, E]), ([F, E, E, E, E, F, T, E, T, E, F, E, E, E, T], [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_710 (And.intro z_341 (And.intro z_712 trivial)))

theorem z_1331 : le (tf [F, E, E, E, E, E, T, F, T, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, F, E, T, E, E] [([F, E, E, E, E, E, T, F, E, T, F, E, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E]), ([F, E, E, E, E, E, T, F, T, E, F, E, E, T, E], [F, E, E, E, E, F, T, E, T, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 (And.intro z_1330 trivial))

theorem z_1332 : le (tf [E, F, E, E, E, E, T, F, T, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, E, F, T, E, E, E] [([E, F, E, E, E, E, T, F, E, T, F, T, E, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]), ([E, F, E, E, E, E, T, F, T, E, F, E, T, E, E], [F, E, E, E, E, E, T, F, T, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_1331 trivial))

theorem z_1333 : le (tf [E, F, E, E, E, T, E, F, E, T, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, F, E, T, F, T, E, E, E] [([E, F, E, E, E, E, T, F, E, T, F, T, E, E, E], [F, E, E, E, E, E, T, F, E, T, F, T, E, E, E]), ([E, F, E, E, E, T, E, F, E, T, F, E, T, E, E], [F, E, E, E, E, T, E, F, E, T, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_625 trivial))

theorem z_1334 : le (tf [E, E, F, E, E, T, E, F, T, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, T, E, F, T, E, E, E] [([E, E, F, E, E, E, T, F, T, E, F, T, E, E, E], [E, F, E, E, E, E, T, F, T, E, F, T, E, E, E]), ([E, E, F, E, E, T, E, F, E, T, F, T, E, E, E], [E, F, E, E, E, T, E, F, E, T, F, T, E, E, E]), ([E, E, F, E, E, T, E, F, T, E, F, E, T, E, E], [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1332 (And.intro z_1333 (And.intro z_653 trivial)))

theorem z_1335 : le (tf [E, F, E, E, E, T, T, F, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, F, E, E, T, E] [([E, F, E, E, E, T, E, F, T, E, F, E, E, T, E], [E, F, E, E, E, T, F, E, T, E, F, E, E, T, E]), ([E, F, E, E, E, T, T, F, E, E, F, E, E, E, T], [F, E, E, E, E, T, T, F, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_652 (And.intro z_750 trivial))

theorem z_1336 : le (tf [E, E, F, E, E, T, T, F, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, E, F, E, T, E, E] [([E, E, F, E, E, T, E, F, T, E, F, E, T, E, E], [E, E, F, E, E, T, F, E, T, E, F, E, T, E, E]), ([E, E, F, E, E, T, T, F, E, E, F, E, E, T, E], [E, F, E, E, E, T, T, F, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_653 (And.intro z_1335 trivial))

theorem z_1337 : le (tf [E, E, E, F, E, T, T, F, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, E, F, T, E, E, E] [([E, E, E, F, E, T, E, F, T, E, F, T, E, E, E], [E, E, F, E, E, T, E, F, T, E, F, T, E, E, E]), ([E, E, E, F, E, T, T, F, E, E, F, E, T, E, E], [E, E, F, E, E, T, T, F, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1334 (And.intro z_1336 trivial))

theorem z_1338 : le (tf [F, E, E, E, E, E, E, F, T, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, T, F, T, T, E, E, E] [([F, E, E, E, E, E, E, F, T, F, T, E, T, E, E], [F, E, E, E, E, E, F, E, T, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_668 trivial)

theorem z_1339 : le (tf [F, E, E, E, E, F, T, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, F, E, T, T, E, E] [([F, E, E, E, E, F, E, T, E, F, E, T, T, E, E], [F, E, E, E, F, E, E, T, E, F, E, T, T, E, E]), ([F, E, E, E, E, F, T, E, E, F, E, T, E, T, E], [F, E, E, E, F, E, T, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_694 trivial))

theorem z_1340 : le (tf [F, E, E, E, E, E, T, F, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, F, T, E, T, E, E] [([F, E, E, E, E, E, E, F, T, F, T, E, T, E, E], [F, E, E, E, E, E, F, E, T, F, T, E, T, E, E]), ([F, E, E, E, E, E, T, F, E, F, E, T, T, E, E], [F, E, E, E, E, F, T, E, E, F, E, T, T, E, E]), ([F, E, E, E, E, E, T, F, E, F, T, E, E, T, E], [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_668 (And.intro z_1339 (And.intro z_711 trivial)))

theorem z_1341 : le (tf [E, F, E, E, E, E, T, F, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, E, F, T, T, E, E, E] [([E, F, E, E, E, E, E, F, T, F, T, T, E, E, E], [F, E, E, E, E, E, E, F, T, F, T, T, E, E, E]), ([E, F, E, E, E, E, T, F, E, F, T, E, T, E, E], [F, E, E, E, E, E, T, F, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1338 (And.intro z_1340 trivial))

theorem z_1342 : le (tf [E, F, E, E, E, E, T, F, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, F, T, F, E, E, T, E, E] [([E, F, E, E, E, E, T, F, E, F, T, E, T, E, E], [F, E, E, E, E, E, T, F, E, F, T, E, T, E, E]), ([E, F, E, E, E, E, T, F, T, F, E, E, E, T, E], [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1340 (And.intro z_713 trivial))

theorem z_1343 : le (tf [E, E, F, E, E, E, T, F, T, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, F, T, F, E, T, E, E, E] [([E, E, F, E, E, E, T, F, E, F, T, T, E, E, E], [E, F, E, E, E, E, T, F, E, F, T, T, E, E, E]), ([E, E, F, E, E, E, T, F, T, F, E, E, T, E, E], [E, F, E, E, E, E, T, F, T, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1341 (And.intro z_1342 trivial))

theorem z_1344 : le (tf [E, E, F, E, E, T, E, F, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, F, E, F, T, T, E, E, E] [([E, E, F, E, E, E, T, F, E, F, T, T, E, E, E], [E, F, E, E, E, E, T, F, E, F, T, T, E, E, E]), ([E, E, F, E, E, T, E, F, E, F, T, E, T, E, E], [E, E, F, E, E, T, F, E, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1341 (And.intro z_690 trivial))

theorem z_1345 : le (tf [E, E, E, F, E, T, E, F, T, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, F, T, F, E, T, E, E, E] [([E, E, E, F, E, E, T, F, T, F, E, T, E, E, E], [E, E, F, E, E, E, T, F, T, F, E, T, E, E, E]), ([E, E, E, F, E, T, E, F, E, F, T, T, E, E, E], [E, E, F, E, E, T, E, F, E, F, T, T, E, E, E]), ([E, E, E, F, E, T, E, F, T, F, E, E, T, E, E], [E, E, E, F, E, T, F, E, T, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1343 (And.intro z_1344 (And.intro z_693 trivial)))

theorem z_1346 : le (tf [F, E, E, E, E, F, E, E, T, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, T, F, T, T, E, E, E] [([F, E, E, E, E, F, E, E, T, F, T, E, T, E, E], [F, E, E, E, F, E, E, E, T, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 trivial)

theorem z_1347 : le (tf [F, E, E, E, E, E, F, T, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, F, T, T, E, E, E] [([F, E, E, E, E, E, F, E, T, F, T, T, E, E, E], [F, E, E, E, E, F, E, E, T, F, T, T, E, E, E]), ([F, E, E, E, E, E, F, T, E, F, T, E, T, E, E], [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1346 (And.intro z_363 trivial))

theorem z_1348 : le (tf [E, F, E, E, E, T, F, E, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, F, T, T, E, E, E] [([E, F, E, E, E, E, F, T, E, F, T, T, E, E, E], [F, E, E, E, E, E, F, T, E, F, T, T, E, E, E]), ([E, F, E, E, E, T, F, E, E, F, T, E, T, E, E], [F, E, E, E, E, T, F, E, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1347 (And.intro z_399 trivial))

theorem z_1349 : le (tf [E, F, E, E, T, E, E, F, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, E, F, T, T, E, E, E] [([E, F, E, E, E, T, E, F, E, F, T, T, E, E, E], [E, F, E, E, E, T, F, E, E, F, T, T, E, E, E]), ([E, F, E, E, T, E, E, F, E, F, T, E, T, E, E], [E, F, E, E, T, E, F, E, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1348 (And.intro z_699 trivial))

theorem z_1350 : le (tf [E, E, F, T, E, E, E, F, E, F, T, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, F, E, F, T, T, E, E, E] [([E, E, F, E, T, E, E, F, E, F, T, T, E, E, E], [E, F, E, E, T, E, E, F, E, F, T, T, E, E, E]), ([E, E, F, T, E, E, E, F, E, F, T, E, T, E, E], [E, E, F, T, E, E, F, E, E, F, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1349 (And.intro z_708 trivial))

theorem z_1351 : le (tf [E, E, E, T, F, E, E, F, T, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, F, T, F, E, T, E, E, E] [([E, E, E, E, F, T, E, F, T, F, E, T, E, E, E], [E, E, E, F, E, T, E, F, T, F, E, T, E, E, E]), ([E, E, E, T, F, E, E, F, E, F, T, T, E, E, E], [E, E, F, T, E, E, E, F, E, F, T, T, E, E, E]), ([E, E, E, T, F, E, E, F, T, F, E, E, T, E, E], [E, E, E, T, F, E, F, E, T, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1345 (And.intro z_1350 (And.intro z_719 trivial)))

theorem z_1352 : le (tf [E, F, E, E, E, T, T, F, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, F, E, E, E, E, T] [([E, F, E, E, E, T, E, F, T, F, E, E, E, E, T], [E, F, E, E, E, T, F, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_691 trivial)

theorem z_1353 : le (tf [E, E, F, E, E, T, T, F, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, F, E, E, E, T, E] [([E, E, F, E, E, T, E, F, T, F, E, E, E, T, E], [E, E, F, E, E, T, F, E, T, F, E, E, E, T, E]), ([E, E, F, E, E, T, T, F, E, F, E, E, E, E, T], [E, F, E, E, E, T, T, F, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_692 (And.intro z_1352 trivial))

theorem z_1354 : le (tf [E, E, E, F, E, T, T, F, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, F, E, E, T, E, E] [([E, E, E, F, E, T, E, F, T, F, E, E, T, E, E], [E, E, E, F, E, T, F, E, T, F, E, E, T, E, E]), ([E, E, E, F, E, T, T, F, E, F, E, E, E, T, E], [E, E, F, E, E, T, T, F, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_693 (And.intro z_1353 trivial))

theorem z_1355 : le (tf [F, E, E, E, E, T, T, F, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, T, F, F, E, E, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1356 : le (tf [E, F, E, E, E, T, T, F, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, F, E, E, E, E, T, E] [([E, F, E, E, E, T, T, F, F, E, E, E, E, E, T], [F, E, E, E, E, T, T, F, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1355 trivial)

theorem z_1357 : le (tf [E, F, E, E, T, E, T, F, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, F, E, E, E, E, E, T] [([E, F, E, E, E, T, T, F, F, E, E, E, E, E, T], [F, E, E, E, E, T, T, F, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1355 trivial)

theorem z_1358 : le (tf [E, E, F, E, T, E, T, F, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, F, E, E, E, E, T, E] [([E, E, F, E, E, T, T, F, F, E, E, E, E, T, E], [E, F, E, E, E, T, T, F, F, E, E, E, E, T, E]), ([E, E, F, E, T, E, T, F, F, E, E, E, E, E, T], [E, F, E, E, T, E, T, F, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1356 (And.intro z_1357 trivial))

theorem z_1359 : le (tf [E, F, E, T, E, E, T, F, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, F, E, E, E, E, T] [([E, F, E, E, T, E, T, F, E, F, E, E, E, E, T], [E, F, E, E, T, E, T, F, F, E, E, E, E, E, T]), ([E, F, E, T, E, E, E, F, T, F, E, E, E, E, T], [E, F, E, T, E, E, F, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1357 (And.intro z_717 trivial))

theorem z_1360 : le (tf [E, E, F, T, E, E, T, F, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, T, F, E, F, E, E, E, T, E] [([E, E, F, E, T, E, T, F, E, F, E, E, E, T, E], [E, E, F, E, T, E, T, F, F, E, E, E, E, T, E]), ([E, E, F, T, E, E, E, F, T, F, E, E, E, T, E], [E, E, F, T, E, E, F, E, T, F, E, E, E, T, E]), ([E, E, F, T, E, E, T, F, E, F, E, E, E, E, T], [E, F, E, T, E, E, T, F, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1358 (And.intro z_718 (And.intro z_1359 trivial)))

theorem z_1361 : le (tf [E, E, E, T, F, E, T, F, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, F, E, E, T, E, E] [([E, E, E, E, F, T, T, F, E, F, E, E, T, E, E], [E, E, E, F, E, T, T, F, E, F, E, E, T, E, E]), ([E, E, E, T, F, E, E, F, T, F, E, E, T, E, E], [E, E, E, T, F, E, F, E, T, F, E, E, T, E, E]), ([E, E, E, T, F, E, T, F, E, F, E, E, E, T, E], [E, E, F, T, E, E, T, F, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1354 (And.intro z_719 (And.intro z_1360 trivial)))

theorem z_1362 : le (tf [E, E, E, T, F, E, T, F, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, E, F, T, E, E, E] [([E, E, E, E, F, T, T, F, E, E, F, T, E, E, E], [E, E, E, F, E, T, T, F, E, E, F, T, E, E, E]), ([E, E, E, T, F, E, E, F, T, E, F, T, E, E, E], [E, E, E, T, F, E, E, F, T, F, E, T, E, E, E]), ([E, E, E, T, F, E, T, F, E, E, F, E, T, E, E], [E, E, E, T, F, E, T, F, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1337 (And.intro z_1351 (And.intro z_1361 trivial)))

theorem z_1363 : le (tf [E, E, E, T, F, E, T, F, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, E, T, E, F, E, E] [([E, E, E, E, F, T, T, F, E, E, T, E, F, E, E], [E, E, E, F, E, T, T, F, E, E, T, E, F, E, E]), ([E, E, E, T, F, E, E, F, T, E, T, E, F, E, E], [E, E, E, T, F, E, E, F, T, E, T, F, E, E, E]), ([E, E, E, T, F, E, T, F, E, E, E, T, F, E, E], [E, E, E, T, F, E, T, F, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1329 (And.intro z_1325 (And.intro z_1362 trivial)))

theorem z_1364 : le (tf [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E] [([E, E, E, E, F, T, T, F, E, T, E, E, E, F, E], [E, E, E, F, E, T, T, F, E, T, E, E, E, F, E]), ([E, E, E, T, F, E, E, F, T, T, E, E, E, F, E], [E, E, E, T, F, E, E, F, T, T, E, E, F, E, E]), ([E, E, E, T, F, E, T, F, E, E, T, E, E, F, E], [E, E, E, T, F, E, T, F, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1295 (And.intro z_1326 (And.intro z_1363 trivial)))

theorem z_1365 : le (tf [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F] [([E, E, E, E, F, T, T, F, T, E, E, E, E, E, F], [E, E, E, F, E, T, T, F, T, E, E, E, E, E, F]), ([E, E, E, T, F, E, T, F, E, T, E, E, E, E, F], [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1289 (And.intro z_1364 trivial))

theorem z_1366 : le (tf [E, E, E, T, F, E, T, T, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, T, E, F, E, E, E, E, F] [([E, E, E, E, F, T, T, T, E, F, E, E, E, E, F], [E, E, E, F, E, T, T, T, E, F, E, E, E, E, F]), ([E, E, E, T, F, E, T, E, T, F, E, E, E, E, F], [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1285 (And.intro z_1365 trivial))

theorem z_1367 : le (tf [E, E, F, T, E, T, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, T, E, T, E, E, F, E, E, T, E, E, F] [([E, E, F, E, T, T, E, E, F, E, E, T, E, E, F], [E, F, E, E, T, T, E, E, F, E, E, T, E, E, F]), ([E, E, F, T, E, E, T, E, F, E, E, T, E, E, F], [E, E, F, T, E, E, T, F, E, E, E, T, E, E, F]), ([E, E, F, T, E, T, E, E, F, E, E, E, T, E, F], [E, F, E, T, E, T, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1145 (And.intro z_761 (And.intro z_1267 trivial)))

theorem z_1368 : le (tf [E, E, E, T, F, T, E, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, E, F, E, T, E, E, E, F] [([E, E, E, T, F, E, T, E, F, E, T, E, E, E, F], [E, E, E, T, F, E, T, F, E, E, T, E, E, E, F]), ([E, E, E, T, F, T, E, E, F, E, E, T, E, E, F], [E, E, F, T, E, T, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_762 (And.intro z_1367 trivial))

theorem z_1369 : le (tf [E, E, E, T, F, T, E, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, E, T, F, E, E, E, E, F] [([E, E, E, T, F, E, T, E, T, F, E, E, E, E, F], [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F]), ([E, E, E, T, F, T, E, E, E, F, T, E, E, E, F], [E, E, E, T, F, T, E, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1365 (And.intro z_1368 trivial))

theorem z_1370 : le (tf [E, E, E, T, F, T, E, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, T, E, E, F, E, E, E, F] [([E, E, E, T, F, E, T, T, E, E, F, E, E, E, F], [E, E, E, T, F, E, T, T, E, F, E, E, E, E, F]), ([E, E, E, T, F, T, E, E, T, E, F, E, E, E, F], [E, E, E, T, F, T, E, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1366 (And.intro z_1369 trivial))

theorem z_1371 : le (tf [E, E, E, T, F, T, T, E, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, T, E, E, E, E, F, E, E, F] [([E, E, E, T, F, T, E, T, E, E, E, F, E, E, F], [E, E, E, T, F, T, E, T, E, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1370 trivial)

theorem z_1372 : le (tf [E, E, F, E, T, E, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, T, F, E, E, E, E, F] [([E, E, F, E, E, T, E, T, T, F, E, E, E, E, F], [E, F, E, E, E, T, E, T, T, F, E, E, E, E, F]), ([E, E, F, E, T, E, E, T, E, F, T, E, E, E, F], [E, F, E, E, T, E, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1283 (And.intro z_499 trivial))

theorem z_1373 : le (tf [E, E, T, F, E, E, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, T, F, E, E, E, E, F] [([E, E, E, F, T, E, E, T, T, F, E, E, E, E, F], [E, E, F, E, T, E, E, T, T, F, E, E, E, E, F]), ([E, E, T, F, E, E, E, T, E, F, T, E, E, E, F], [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1372 (And.intro z_935 trivial))

theorem z_1374 : le (tf [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F] [([E, E, E, T, F, E, T, E, T, F, E, E, E, E, F], [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F]), ([E, E, T, E, F, E, E, T, T, F, E, E, E, E, F], [E, E, T, F, E, E, E, T, T, F, E, E, E, E, F]), ([E, E, T, E, F, E, T, E, E, F, T, E, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1365 (And.intro z_1373 (And.intro z_955 trivial)))

theorem z_1375 : le (tf [E, E, T, E, F, E, T, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, T, E, E, F, E, E, E, F] [([E, E, E, T, F, E, T, T, E, E, F, E, E, E, F], [E, E, E, T, F, E, T, T, E, F, E, E, E, E, F]), ([E, E, T, E, F, E, T, E, T, E, F, E, E, E, F], [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1366 (And.intro z_1374 trivial))

theorem z_1376 : le (tf [F, E, E, T, E, E, T, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, T, F, E, E, E, E, F, E, T] [([F, E, E, E, T, E, T, F, E, E, E, E, F, E, T], [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T]), ([F, E, E, T, E, E, E, F, T, E, E, E, F, E, T], [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_755 (And.intro z_1322 trivial))

theorem z_1377 : le (tf [E, F, E, T, E, E, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, E, E, F, T, E] [([E, F, E, E, T, E, T, F, E, E, E, E, F, T, E], [F, E, E, E, T, E, T, F, E, E, E, E, F, T, E]), ([E, F, E, T, E, E, E, F, T, E, E, E, F, T, E], [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E]), ([E, F, E, T, E, E, T, F, E, E, E, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_756 (And.intro z_1323 (And.intro z_1376 trivial)))

theorem z_1378 : le (tf [E, F, E, T, E, T, E, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, F, E, E, E, E, F, E, T] [([E, F, E, E, T, T, E, F, E, E, E, E, F, E, T], [E, F, E, E, T, T, F, E, E, E, E, E, F, E, T]), ([E, F, E, T, E, E, T, F, E, E, E, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1226 (And.intro z_1376 trivial))

theorem z_1379 : le (tf [E, E, F, T, E, T, E, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, T, E, F, E, E, E, E, F, T, E] [([E, E, F, E, T, T, E, F, E, E, E, E, F, T, E], [E, E, F, E, T, T, F, E, E, E, E, E, F, T, E]), ([E, E, F, T, E, E, T, F, E, E, E, E, F, T, E], [E, F, E, T, E, E, T, F, E, E, E, E, F, T, E]), ([E, E, F, T, E, T, E, F, E, E, E, E, F, E, T], [E, F, E, T, E, T, E, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1227 (And.intro z_1377 (And.intro z_1378 trivial)))

theorem z_1380 : le (tf [E, E, E, T, F, T, E, F, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, F, E, E, E, T, F, E, E] [([E, E, E, T, F, E, T, F, E, E, E, T, F, E, E], [E, E, E, T, F, E, T, F, E, E, F, T, E, E, E]), ([E, E, E, T, F, T, E, F, E, E, E, E, F, T, E], [E, E, F, T, E, T, E, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1362 (And.intro z_1379 trivial))

theorem z_1381 : le (tf [E, E, E, T, F, T, E, F, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, F, E, E, T, E, E, F, E] [([E, E, E, T, F, E, T, F, E, E, T, E, E, F, E], [E, E, E, T, F, E, T, F, E, E, T, E, F, E, E]), ([E, E, E, T, F, T, E, F, E, E, E, T, E, F, E], [E, E, E, T, F, T, E, F, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1363 (And.intro z_1380 trivial))

theorem z_1382 : le (tf [E, E, E, T, F, T, E, F, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, F, E, T, E, E, E, E, F] [([E, E, E, T, F, E, T, F, E, T, E, E, E, E, F], [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E]), ([E, E, E, T, F, T, E, F, E, E, T, E, E, E, F], [E, E, E, T, F, T, E, F, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1364 (And.intro z_1381 trivial))

theorem z_1383 : le (tf [E, E, F, E, T, E, E, F, T, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, F, T, T, E, E, E, E, F] [([E, E, F, E, E, T, E, F, T, T, E, E, E, E, F], [E, F, E, E, E, T, E, F, T, T, E, E, E, E, F]), ([E, E, F, E, T, E, E, F, T, E, T, E, E, E, F], [E, F, E, E, T, E, E, F, T, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1287 (And.intro z_739 trivial))

theorem z_1384 : le (tf [E, E, T, F, E, E, E, F, T, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, F, T, T, E, E, E, E, F] [([E, E, E, F, T, E, E, F, T, T, E, E, E, E, F], [E, E, F, E, T, E, E, F, T, T, E, E, E, E, F]), ([E, E, T, F, E, E, E, F, T, E, T, E, E, E, F], [E, E, T, F, E, E, F, E, T, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1383 (And.intro z_1154 trivial))

theorem z_1385 : le (tf [E, E, T, E, F, E, T, F, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, F, E, T, E, E, E, E, F] [([E, E, E, T, F, E, T, F, E, T, E, E, E, E, F], [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E]), ([E, E, T, E, F, E, E, F, T, T, E, E, E, E, F], [E, E, T, F, E, E, E, F, T, T, E, E, E, E, F]), ([E, E, T, E, F, E, T, F, E, E, T, E, E, E, F], [E, E, T, F, E, E, T, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1364 (And.intro z_1384 (And.intro z_1219 trivial)))

theorem z_1386 : le (tf [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F] [([E, E, E, T, F, T, E, E, F, T, E, E, E, E, F], [E, E, E, T, F, T, E, F, E, T, E, E, E, E, F]), ([E, E, T, E, F, E, T, E, F, T, E, E, E, E, F], [E, E, T, E, F, E, T, F, E, T, E, E, E, E, F]), ([E, E, T, E, F, T, E, E, F, E, T, E, E, E, F], [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1382 (And.intro z_1385 (And.intro z_1241 trivial)))

theorem z_1387 : le (tf [E, E, T, E, F, T, E, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, E, E, T, E, F, E, E, E, F] [([E, E, E, T, F, T, E, E, T, E, F, E, E, E, F], [E, E, E, T, F, T, E, E, T, F, E, E, E, E, F]), ([E, E, T, E, F, E, T, E, T, E, F, E, E, E, F], [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F]), ([E, E, T, E, F, T, E, E, E, T, F, E, E, E, F], [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1369 (And.intro z_1374 (And.intro z_1386 trivial)))

theorem z_1388 : le (tf [E, E, T, E, F, T, E, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, E, T, E, E, E, F, E, E, F] [([E, E, E, T, F, T, E, T, E, E, E, F, E, E, F], [E, E, E, T, F, T, E, T, E, E, F, E, E, E, F]), ([E, E, T, E, F, E, T, T, E, E, E, F, E, E, F], [E, E, T, E, F, E, T, T, E, E, F, E, E, E, F]), ([E, E, T, E, F, T, E, E, T, E, E, F, E, E, F], [E, E, T, E, F, T, E, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1370 (And.intro z_1375 (And.intro z_1387 trivial)))

theorem z_1389 : le (tf [E, E, T, E, F, T, T, E, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, T, E, E, E, E, E, F, E, F] [([E, E, E, T, F, T, T, E, E, E, E, E, F, E, F], [E, E, E, T, F, T, T, E, E, E, E, F, E, E, F]), ([E, E, T, E, F, T, E, T, E, E, E, E, F, E, F], [E, E, T, E, F, T, E, T, E, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1371 (And.intro z_1388 trivial))

theorem z_1390 : le (tf [E, E, F, E, T, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, F, E, E, E, E, E, T, F] [([E, E, F, E, T, E, T, F, E, E, E, E, E, T, F], [E, F, E, E, T, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_947 trivial)

theorem z_1391 : le (tf [E, E, T, F, E, T, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, F, E, E, E, E, E, T, F] [([E, E, E, F, T, T, E, F, E, E, E, E, E, T, F], [E, E, F, E, T, T, E, F, E, E, E, E, E, T, F]), ([E, E, T, F, E, E, T, F, E, E, E, E, E, T, F], [E, F, T, E, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1390 (And.intro z_952 trivial))

theorem z_1392 : le (tf [E, E, T, T, F, E, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, F, E, E, E, E, E, T, F] [([E, E, T, E, F, T, E, F, E, E, E, E, E, T, F], [E, E, T, F, E, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1391 trivial)

theorem z_1393 : le (tf [E, E, T, T, F, E, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, F, E, E, E, T, E, F] [([E, E, T, E, F, T, E, E, F, E, E, E, T, E, F], [E, E, T, F, E, T, E, E, F, E, E, E, T, E, F]), ([E, E, T, T, F, E, E, E, F, E, E, E, E, T, F], [E, E, T, T, F, E, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_976 (And.intro z_1392 trivial))

theorem z_1394 : le (tf [E, E, T, T, F, E, E, E, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, F, E, T, E, E, F] [([E, E, T, E, F, T, E, E, E, F, E, T, E, E, F], [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F]), ([E, E, T, T, F, E, E, E, E, F, E, E, T, E, F], [E, E, T, T, F, E, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_977 (And.intro z_1393 trivial))

theorem z_1395 : le (tf [E, E, T, T, F, E, E, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, E, T, F, E, E, E, F] [([E, E, T, E, F, T, E, E, E, T, F, E, E, E, F], [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F]), ([E, E, T, T, F, E, E, E, E, E, F, T, E, E, F], [E, E, T, T, F, E, E, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1386 (And.intro z_1394 trivial))

theorem z_1396 : le (tf [E, E, T, T, F, E, E, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, T, E, E, F, E, E, F] [([E, E, T, E, F, T, E, E, T, E, E, F, E, E, F], [E, E, T, E, F, T, E, E, T, E, F, E, E, E, F]), ([E, E, T, T, F, E, E, E, E, T, E, F, E, E, F], [E, E, T, T, F, E, E, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1387 (And.intro z_1395 trivial))

theorem z_1397 : le (tf [E, E, T, T, F, E, E, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, T, E, E, E, E, F, E, F] [([E, E, T, E, F, T, E, T, E, E, E, E, F, E, F], [E, E, T, E, F, T, E, T, E, E, E, F, E, E, F]), ([E, E, T, T, F, E, E, E, T, E, E, E, F, E, F], [E, E, T, T, F, E, E, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1388 (And.intro z_1396 trivial))

theorem z_1398 : le (tf [E, E, T, T, F, E, T, E, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, T, E, E, E, E, E, E, F, F] [([E, E, T, E, F, T, T, E, E, E, E, E, E, F, F], [E, E, T, E, F, T, T, E, E, E, E, E, F, E, F]), ([E, E, T, T, F, E, E, T, E, E, E, E, E, F, F], [E, E, T, T, F, E, E, T, E, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1389 (And.intro z_1397 trivial))

theorem z_1399 : le (tf [E, E, E, T, T, F, F, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, F, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1400 : le (tf [E, E, E, T, T, F, F, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, E, F, E, T, E] [([E, E, E, T, T, F, F, E, E, E, E, F, E, E, T], [E, E, E, T, T, F, F, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1399 trivial)

theorem z_1401 : le (tf [E, E, E, T, T, F, F, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, E, T, F, E, E] [([E, E, E, T, T, F, F, E, E, E, E, E, F, T, E], [E, E, E, T, T, F, F, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1400 trivial)

theorem z_1402 : le (tf [E, E, E, T, T, F, F, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, E, T, E, E, F, E] [([E, E, E, T, T, F, F, E, E, E, E, T, E, F, E], [E, E, E, T, T, F, F, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1401 trivial)

theorem z_1403 : le (tf [E, E, E, T, T, F, F, E, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, F, E, E, T, E, E, E, E, F] [([E, E, E, T, T, F, F, E, E, E, T, E, E, E, F], [E, E, E, T, T, F, F, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1402 trivial)

theorem z_1404 : le (tf [E, E, E, T, T, F, E, F, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, F, T, E, E, E, E, E, F] [([E, E, E, T, E, F, T, F, T, E, E, E, E, E, F], [E, E, E, T, F, E, T, F, T, E, E, E, E, E, F]), ([E, E, E, T, T, F, E, F, E, T, E, E, E, E, F], [E, E, E, T, T, F, F, E, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1365 (And.intro z_1403 trivial))

theorem z_1405 : le (tf [E, E, E, T, T, F, E, T, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, E, T, E, F, E, E, E, E, F] [([E, E, E, T, E, F, T, T, E, F, E, E, E, E, F], [E, E, E, T, F, E, T, T, E, F, E, E, E, E, F]), ([E, E, E, T, T, F, E, E, T, F, E, E, E, E, F], [E, E, E, T, T, F, E, F, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1366 (And.intro z_1404 trivial))

theorem z_1406 : le (tf [E, E, E, T, T, F, T, E, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, F, T, E, E, E, F, E, E, E, F] [([E, E, E, T, T, F, E, T, E, E, F, E, E, E, F], [E, E, E, T, T, F, E, T, E, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1405 trivial)

theorem z_1407 : le (tf [E, E, T, E, T, F, E, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, E, T, F, E, E, E, E, F] [([E, E, E, T, T, F, E, E, T, F, E, E, E, E, F], [E, E, E, T, T, F, E, F, T, E, E, E, E, E, F]), ([E, E, T, E, E, F, T, E, T, F, E, E, E, E, F], [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F]), ([E, E, T, E, T, F, E, E, E, F, T, E, E, E, F], [E, E, T, F, T, E, E, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1404 (And.intro z_1374 (And.intro z_1245 trivial)))

theorem z_1408 : le (tf [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F] [([E, E, E, T, T, F, E, T, E, E, F, E, E, E, F], [E, E, E, T, T, F, E, T, E, F, E, E, E, E, F]), ([E, E, T, E, E, F, T, T, E, E, F, E, E, E, F], [E, E, T, E, F, E, T, T, E, E, F, E, E, E, F]), ([E, E, T, E, T, F, E, E, T, E, F, E, E, E, F], [E, E, T, E, T, F, E, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1405 (And.intro z_1375 (And.intro z_1407 trivial)))

theorem z_1409 : le (tf [E, E, T, E, T, F, T, E, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, T, E, E, E, E, F, E, E, F] [([E, E, E, T, T, F, T, E, E, E, E, F, E, E, F], [E, E, E, T, T, F, T, E, E, E, F, E, E, E, F]), ([E, E, T, E, T, F, E, T, E, E, E, F, E, E, F], [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1406 (And.intro z_1408 trivial))

theorem z_1410 : le (tf [E, T, E, E, F, E, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, T, T, F, E, E, E, E, F] [([E, E, T, E, F, E, E, T, T, F, E, E, E, E, F], [E, E, T, F, E, E, E, T, T, F, E, E, E, E, F]), ([E, T, E, E, F, E, E, T, E, F, T, E, E, E, F], [E, T, E, F, E, E, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1373 (And.intro z_1246 trivial))

theorem z_1411 : le (tf [E, T, E, E, E, F, T, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, T, E, T, F, E, E, E, E, F] [([E, E, T, E, E, F, T, E, T, F, E, E, E, E, F], [E, E, T, E, F, E, T, E, T, F, E, E, E, E, F]), ([E, T, E, E, E, F, E, T, T, F, E, E, E, E, F], [E, T, E, E, F, E, E, T, T, F, E, E, E, E, F]), ([E, T, E, E, E, F, T, E, E, F, T, E, E, E, F], [E, T, E, E, F, E, T, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1374 (And.intro z_1410 (And.intro z_1248 trivial)))

theorem z_1412 : le (tf [E, T, E, E, E, F, T, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, T, T, E, E, F, E, E, E, F] [([E, E, T, E, E, F, T, T, E, E, F, E, E, E, F], [E, E, T, E, F, E, T, T, E, E, F, E, E, E, F]), ([E, T, E, E, E, F, T, E, T, E, F, E, E, E, F], [E, T, E, E, E, F, T, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1375 (And.intro z_1411 trivial))

theorem z_1413 : le (tf [F, E, E, E, E, F, E, T, T, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, T, E, F, E, T, E, E] [([F, E, E, E, E, F, E, T, E, T, F, E, T, E, E], [F, E, E, E, F, E, E, T, E, T, F, E, T, E, E]), ([F, E, E, E, E, F, E, T, T, E, F, E, E, T, E], [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_710 trivial))

theorem z_1414 : le (tf [E, F, E, E, E, F, T, E, T, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, T, E, F, E, T, E, E] [([E, F, E, E, E, F, E, T, T, E, F, E, T, E, E], [F, E, E, E, E, F, E, T, T, E, F, E, T, E, E]), ([E, F, E, E, E, F, T, E, E, T, F, E, T, E, E], [F, E, E, E, E, F, T, E, E, T, F, E, T, E, E]), ([E, F, E, E, E, F, T, E, T, E, F, E, E, T, E], [F, E, E, E, E, F, T, E, T, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1413 (And.intro z_342 (And.intro z_1330 trivial)))

theorem z_1415 : le (tf [E, E, F, E, E, F, T, T, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, F, T, T, E, E, F, E, T, E, E] [([E, E, F, E, E, F, T, E, T, E, F, E, T, E, E], [E, F, E, E, E, F, T, E, T, E, F, E, T, E, E]), ([E, E, F, E, E, F, T, T, E, E, F, E, E, T, E], [E, F, E, E, E, F, T, T, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1414 (And.intro z_721 trivial))

theorem z_1416 : le (tf [E, F, E, E, E, F, E, T, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, E, T, T, F, E, E, T, E, E] [([E, F, E, E, E, F, E, T, E, F, T, E, T, E, E], [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E]), ([E, F, E, E, E, F, E, T, T, F, E, E, E, T, E], [F, E, E, E, E, F, E, T, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_363 (And.intro z_710 trivial))

theorem z_1417 : le (tf [E, F, E, E, E, F, T, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, E, F, T, E, T, E, E] [([E, F, E, E, E, F, E, T, E, F, T, E, T, E, E], [F, E, E, E, E, F, E, T, E, F, T, E, T, E, E]), ([E, F, E, E, E, F, T, E, E, F, E, T, T, E, E], [F, E, E, E, E, F, T, E, E, F, E, T, T, E, E]), ([E, F, E, E, E, F, T, E, E, F, T, E, E, T, E], [F, E, E, E, E, F, T, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_363 (And.intro z_1339 (And.intro z_711 trivial)))

theorem z_1418 : le (tf [E, E, F, E, E, F, T, E, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, F, T, E, T, F, E, E, T, E, E] [([E, E, F, E, E, F, E, T, T, F, E, E, T, E, E], [E, F, E, E, E, F, E, T, T, F, E, E, T, E, E]), ([E, E, F, E, E, F, T, E, E, F, T, E, T, E, E], [E, F, E, E, E, F, T, E, E, F, T, E, T, E, E]), ([E, E, F, E, E, F, T, E, T, F, E, E, E, T, E], [E, F, E, E, E, F, T, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1416 (And.intro z_1417 (And.intro z_713 trivial)))

theorem z_1419 : le (tf [E, F, E, E, T, F, E, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, F, E, T, T, E, E] [([E, F, E, E, E, F, T, E, E, F, E, T, T, E, E], [F, E, E, E, E, F, T, E, E, F, E, T, T, E, E]), ([E, F, E, E, T, F, E, E, E, F, E, T, E, T, E], [F, E, E, E, T, F, E, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1339 (And.intro z_696 trivial))

theorem z_1420 : le (tf [E, E, F, E, T, F, E, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, E, F, T, E, T, E, E] [([E, E, F, E, E, F, T, E, E, F, T, E, T, E, E], [E, F, E, E, E, F, T, E, E, F, T, E, T, E, E]), ([E, E, F, E, T, F, E, E, E, F, E, T, T, E, E], [E, F, E, E, T, F, E, E, E, F, E, T, T, E, E]), ([E, E, F, E, T, F, E, E, E, F, T, E, E, T, E], [E, F, E, E, T, F, E, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1417 (And.intro z_1419 (And.intro z_714 trivial)))

theorem z_1421 : le (tf [E, E, E, F, T, F, E, E, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, F, E, E, T, F, E, E, T, E, E] [([E, E, E, F, E, F, T, E, T, F, E, E, T, E, E], [E, E, F, E, E, F, T, E, T, F, E, E, T, E, E]), ([E, E, E, F, T, F, E, E, E, F, T, E, T, E, E], [E, E, F, E, T, F, E, E, E, F, T, E, T, E, E]), ([E, E, E, F, T, F, E, E, T, F, E, E, E, T, E], [E, E, F, E, T, F, E, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1418 (And.intro z_1420 (And.intro z_716 trivial)))

theorem z_1422 : le (tf [E, E, E, F, T, F, E, T, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, F, E, T, E, E, F, E, T, E, E] [([E, E, E, F, E, F, T, T, E, E, F, E, T, E, E], [E, E, F, E, E, F, T, T, E, E, F, E, T, E, E]), ([E, E, E, F, T, F, E, E, T, E, F, E, T, E, E], [E, E, E, F, T, F, E, E, T, F, E, E, T, E, E]), ([E, E, E, F, T, F, E, T, E, E, F, E, E, T, E], [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1415 (And.intro z_1421 (And.intro z_723 trivial)))

theorem z_1423 : le (tf [E, E, F, E, T, T, F, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, E, F, E, E, T, E] [([E, E, F, E, T, E, F, T, E, E, F, E, E, T, E], [E, E, F, E, T, F, E, T, E, E, F, E, E, T, E]), ([E, E, F, E, T, T, F, E, E, E, F, E, E, E, T], [E, F, E, E, T, T, F, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_723 (And.intro z_1235 trivial))

theorem z_1424 : le (tf [E, E, E, F, T, T, F, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, T, F, E, E, E, F, E, T, E, E] [([E, E, E, F, T, E, F, T, E, E, F, E, T, E, E], [E, E, E, F, T, F, E, T, E, E, F, E, T, E, E]), ([E, E, E, F, T, T, F, E, E, E, F, E, E, T, E], [E, E, F, E, T, T, F, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1422 (And.intro z_1423 trivial))

theorem z_1425 : le (tf [F, E, F, E, E, E, E, F, E, E, T, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, F, E, E, T, T, T, E, E] [([F, E, F, E, E, E, E, F, E, E, T, T, E, T, E], [F, F, E, E, E, E, E, F, E, E, T, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 trivial)

theorem z_1426 : le (tf [F, E, E, F, E, E, E, F, E, T, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, F, E, T, E, T, T, E, E] [([F, E, E, F, E, E, E, F, E, E, T, T, T, E, E], [F, E, F, E, E, E, E, F, E, E, T, T, T, E, E]), ([F, E, E, F, E, E, E, F, E, T, E, T, E, T, E], [F, E, F, E, E, E, E, F, E, T, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1425 (And.intro z_375 trivial))

theorem z_1427 : le (tf [F, E, E, E, F, E, E, F, T, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, F, T, E, E, T, T, E, E] [([F, E, E, E, F, E, E, F, E, T, E, T, T, E, E], [F, E, E, F, E, E, E, F, E, T, E, T, T, E, E]), ([F, E, E, E, F, E, E, F, T, E, E, T, E, T, E], [F, E, E, F, E, E, E, F, T, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1426 (And.intro z_378 trivial))

theorem z_1428 : le (tf [E, F, E, E, F, E, T, F, E, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, E, T, F, E, E, E, T, T, E, E] [([E, F, E, E, F, E, E, F, T, E, E, T, T, E, E], [F, E, E, E, F, E, E, F, T, E, E, T, T, E, E]), ([E, F, E, E, F, E, T, F, E, E, E, T, E, T, E], [F, E, E, E, F, E, T, F, E, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1427 (And.intro z_383 trivial))

theorem z_1429 : le (tf [E, F, E, E, F, T, E, E, F, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, F, T, E, E, F, E, E, T, T, E, E] [([E, F, E, E, F, E, T, E, F, E, E, T, T, E, E], [E, F, E, E, F, E, T, F, E, E, E, T, T, E, E]), ([E, F, E, E, F, T, E, E, F, E, E, T, E, T, E], [F, E, E, E, F, T, E, E, F, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1428 (And.intro z_388 trivial))

theorem z_1430 : le (tf [E, F, E, T, F, E, E, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, E, E, E, F, E, T, T, E, E] [([E, F, E, E, F, T, E, E, E, F, E, T, T, E, E], [E, F, E, E, F, T, E, E, F, E, E, T, T, E, E]), ([E, F, E, T, F, E, E, E, E, F, E, T, E, T, E], [F, E, E, T, F, E, E, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1429 (And.intro z_895 trivial))

theorem z_1431 : le (tf [E, F, T, E, E, F, E, E, E, F, E, T, T, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, E, F, E, T, T, E, E] [([E, F, E, T, E, F, E, E, E, F, E, T, T, E, E], [E, F, E, T, F, E, E, E, E, F, E, T, T, E, E]), ([E, F, T, E, E, F, E, E, E, F, E, T, E, T, E], [F, E, T, E, E, F, E, E, E, F, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1430 (And.intro z_1207 trivial))

theorem z_1432 : le (tf [E, E, T, F, E, F, E, E, E, F, T, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, E, F, T, E, T, E, E] [([E, E, E, F, T, F, E, E, E, F, T, E, T, E, E], [E, E, F, E, T, F, E, E, E, F, T, E, T, E, E]), ([E, E, T, F, E, F, E, E, E, F, E, T, T, E, E], [E, F, T, E, E, F, E, E, E, F, E, T, T, E, E]), ([E, E, T, F, E, F, E, E, E, F, T, E, E, T, E], [E, F, T, E, E, F, E, E, E, F, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1420 (And.intro z_1431 (And.intro z_1209 trivial)))

theorem z_1433 : le (tf [E, E, T, F, E, E, F, E, T, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, E, T, F, E, E, T, E, E] [([E, E, E, F, T, E, F, E, T, F, E, E, T, E, E], [E, E, E, F, T, F, E, E, T, F, E, E, T, E, E]), ([E, E, T, F, E, E, F, E, E, F, T, E, T, E, E], [E, E, T, F, E, F, E, E, E, F, T, E, T, E, E]), ([E, E, T, F, E, E, F, E, T, F, E, E, E, T, E], [E, E, T, F, E, F, E, E, T, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1421 (And.intro z_1432 (And.intro z_1212 trivial)))

theorem z_1434 : le (tf [E, E, T, F, E, E, F, T, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, E, E, F, E, T, E, E] [([E, E, E, F, T, E, F, T, E, E, F, E, T, E, E], [E, E, E, F, T, F, E, T, E, E, F, E, T, E, E]), ([E, E, T, F, E, E, F, E, T, E, F, E, T, E, E], [E, E, T, F, E, E, F, E, T, F, E, E, T, E, E]), ([E, E, T, F, E, E, F, T, E, E, F, E, E, T, E], [E, E, T, F, E, F, E, T, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1422 (And.intro z_1433 (And.intro z_1214 trivial)))

theorem z_1435 : le (tf [F, E, E, E, E, F, E, T, F, T, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, F, T, E, E, E, E, T] [([F, E, E, E, E, F, E, T, F, E, T, E, E, E, T], [F, E, E, E, F, E, E, T, F, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_392 trivial)

theorem z_1436 : le (tf [F, E, E, E, E, T, F, E, F, T, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, F, T, E, E, E, E, T] [([F, E, E, E, E, E, F, T, F, T, E, E, E, E, T], [F, E, E, E, E, F, E, T, F, T, E, E, E, E, T]), ([F, E, E, E, E, T, F, E, F, E, T, E, E, E, T], [F, E, E, E, F, T, E, E, F, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1435 (And.intro z_397 trivial))

theorem z_1437 : le (tf [E, F, E, E, E, T, F, T, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, F, E, E, E, E, E, T] [([E, F, E, E, E, T, F, E, F, T, E, E, E, E, T], [F, E, E, E, E, T, F, E, F, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1436 trivial)

theorem z_1438 : le (tf [E, F, E, E, T, E, F, T, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, F, E, E, E, E, T] [([E, F, E, E, E, T, F, T, E, F, E, E, E, E, T], [E, F, E, E, E, T, F, T, F, E, E, E, E, E, T]), ([E, F, E, E, T, E, F, E, T, F, E, E, E, E, T], [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1437 (And.intro z_715 trivial))

theorem z_1439 : le (tf [E, E, F, E, T, T, F, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, F, E, E, F, E, E, E, E, T] [([E, E, F, E, T, E, F, T, E, F, E, E, E, E, T], [E, F, E, E, T, E, F, T, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1438 trivial)

theorem z_1440 : le (tf [E, F, E, E, E, F, T, T, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, T, E, F, E, E, E, E, T] [([E, F, E, E, E, F, T, E, T, F, E, E, E, E, T], [F, E, E, E, E, F, T, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_712 trivial)

theorem z_1441 : le (tf [E, E, F, E, T, F, E, T, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, T, E, F, E, E, E, E, T] [([E, E, F, E, E, F, T, T, E, F, E, E, E, E, T], [E, F, E, E, E, F, T, T, E, F, E, E, E, E, T]), ([E, E, F, E, T, F, E, E, T, F, E, E, E, E, T], [E, F, E, E, T, F, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1440 (And.intro z_715 trivial))

theorem z_1442 : le (tf [E, E, T, F, E, F, E, T, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, T, E, F, E, E, E, E, T] [([E, E, E, F, T, F, E, T, E, F, E, E, E, E, T], [E, E, F, E, T, F, E, T, E, F, E, E, E, E, T]), ([E, E, T, F, E, F, E, E, T, F, E, E, E, E, T], [E, E, T, F, F, E, E, E, T, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1441 (And.intro z_1211 trivial))

theorem z_1443 : le (tf [E, E, T, F, E, T, F, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, F, E, E, E, E, T] [([E, E, E, F, T, T, F, E, E, F, E, E, E, E, T], [E, E, F, E, T, T, F, E, E, F, E, E, E, E, T]), ([E, E, T, F, E, E, F, T, E, F, E, E, E, E, T], [E, E, T, F, E, F, E, T, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1439 (And.intro z_1442 trivial))

theorem z_1444 : le (tf [E, E, T, F, E, T, F, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, F, E, E, T, E] [([E, E, E, F, T, T, F, E, E, E, F, E, E, T, E], [E, E, F, E, T, T, F, E, E, E, F, E, E, T, E]), ([E, E, T, F, E, E, F, T, E, E, F, E, E, T, E], [E, E, T, F, E, F, E, T, E, E, F, E, E, T, E]), ([E, E, T, F, E, T, F, E, E, E, F, E, E, E, T], [E, E, T, F, E, T, F, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1423 (And.intro z_1214 (And.intro z_1443 trivial)))

theorem z_1445 : le (tf [E, E, T, F, E, T, F, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, F, E, E, E, E, F, T, E, E] [([E, E, E, F, T, T, F, E, E, E, E, F, T, E, E], [E, E, E, F, T, T, F, E, E, E, F, E, T, E, E]), ([E, E, T, F, E, E, F, T, E, E, E, F, T, E, E], [E, E, T, F, E, E, F, T, E, E, F, E, T, E, E]), ([E, E, T, F, E, T, F, E, E, E, E, F, E, T, E], [E, E, T, F, E, T, F, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1424 (And.intro z_1434 (And.intro z_1444 trivial)))

theorem z_1446 : le (tf [F, E, E, E, F, T, T, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, T, E, E, E, E, E, E, F, T] [([F, E, E, E, F, T, E, T, E, E, E, E, E, F, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 trivial)

theorem z_1447 : le (tf [E, F, E, T, F, E, T, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, F, E, T, E, E, E, E, E, E, F, T] [([E, F, E, E, F, T, T, E, E, E, E, E, E, F, T], [F, E, E, E, F, T, T, E, E, E, E, E, E, F, T]), ([E, F, E, T, F, E, E, T, E, E, E, E, E, F, T], [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1446 (And.intro z_1232 trivial))

theorem z_1448 : le (tf [E, F, E, T, T, F, E, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, T, F, E, E, E, E, E, E, E, F, T] [([E, F, E, T, E, F, T, E, E, E, E, E, E, F, T], [E, F, E, T, F, E, T, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1447 trivial)

theorem z_1449 : le (tf [E, F, T, E, T, E, F, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, T, E, F, E, E, E, E, E, E, F, T] [([E, F, E, T, T, E, F, E, E, E, E, E, E, F, T], [E, F, E, T, T, F, E, E, E, E, E, E, E, F, T]), ([E, F, T, E, E, T, F, E, E, E, E, E, E, F, T], [E, F, T, E, E, T, F, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1448 (And.intro z_1237 trivial))

theorem z_1450 : le (tf [E, E, T, F, T, E, F, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, T, E, F, E, E, E, E, E, T, F, E] [([E, E, T, F, E, T, F, E, E, E, E, E, T, F, E], [E, E, T, F, E, T, F, E, E, E, E, F, T, E, E]), ([E, E, T, F, T, E, F, E, E, E, E, E, E, F, T], [E, F, T, E, T, E, F, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1445 (And.intro z_1449 trivial))

theorem z_1451 : le (tf [E, E, T, E, T, F, F, E, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, F, E, E, E, E, T, E, F, E] [([E, E, E, T, T, F, F, E, E, E, E, T, E, F, E], [E, E, E, T, T, F, F, E, E, E, E, T, F, E, E]), ([E, E, T, E, T, F, F, E, E, E, E, E, T, F, E], [E, E, T, F, T, E, F, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1401 (And.intro z_1450 trivial))

theorem z_1452 : le (tf [E, E, T, E, T, F, F, E, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, F, E, E, E, T, E, E, E, F] [([E, E, E, T, T, F, F, E, E, E, T, E, E, E, F], [E, E, E, T, T, F, F, E, E, E, T, E, E, F, E]), ([E, E, T, E, T, F, F, E, E, E, E, T, E, E, F], [E, E, T, E, T, F, F, E, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1402 (And.intro z_1451 trivial))

theorem z_1453 : le (tf [E, E, T, E, T, F, E, F, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, F, E, F, E, T, E, E, E, E, F] [([E, E, E, T, T, F, E, F, E, T, E, E, E, E, F], [E, E, E, T, T, F, F, E, E, T, E, E, E, E, F]), ([E, E, T, E, E, F, T, F, E, T, E, E, E, E, F], [E, E, T, E, F, E, T, F, E, T, E, E, E, E, F]), ([E, E, T, E, T, F, E, F, E, E, T, E, E, E, F], [E, E, T, E, T, F, F, E, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1403 (And.intro z_1385 (And.intro z_1452 trivial)))

theorem z_1454 : le (tf [E, T, F, E, E, E, E, F, E, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, E, T, T, E, E, E, F] [([E, E, F, T, E, E, E, F, E, T, T, E, E, E, F], [E, F, E, T, E, E, E, F, E, T, T, E, E, E, F]), ([E, T, F, E, E, E, E, F, E, T, E, T, E, E, F], [E, T, F, E, E, E, F, E, E, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_742 (And.intro z_1054 trivial))

theorem z_1455 : le (tf [E, T, E, F, E, E, E, F, T, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, F, T, E, T, E, E, E, F] [([E, E, T, F, E, E, E, F, T, E, T, E, E, E, F], [E, E, T, F, E, E, F, E, T, E, T, E, E, E, F]), ([E, T, E, F, E, E, E, F, E, T, T, E, E, E, F], [E, T, F, E, E, E, E, F, E, T, T, E, E, E, F]), ([E, T, E, F, E, E, E, F, T, E, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1154 (And.intro z_1454 (And.intro z_1068 trivial)))

theorem z_1456 : le (tf [E, T, E, E, F, E, E, F, T, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, F, T, T, E, E, E, E, F] [([E, E, T, E, F, E, E, F, T, T, E, E, E, E, F], [E, E, T, F, E, E, E, F, T, T, E, E, E, E, F]), ([E, T, E, E, F, E, E, F, T, E, T, E, E, E, F], [E, T, E, F, E, E, E, F, T, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1384 (And.intro z_1455 trivial))

theorem z_1457 : le (tf [E, T, E, E, F, E, T, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, F, E, E, T, E, E, E, F] [([E, E, T, E, F, E, T, F, E, E, T, E, E, E, F], [E, E, T, F, E, E, T, F, E, E, T, E, E, E, F]), ([E, T, E, E, F, E, E, F, T, E, T, E, E, E, F], [E, T, E, F, E, E, E, F, T, E, T, E, E, E, F]), ([E, T, E, E, F, E, T, F, E, E, E, T, E, E, F], [E, T, E, F, E, E, T, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1219 (And.intro z_1455 (And.intro z_1266 trivial)))

theorem z_1458 : le (tf [E, T, E, E, E, F, T, F, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, T, F, E, T, E, E, E, E, F] [([E, E, T, E, E, F, T, F, E, T, E, E, E, E, F], [E, E, T, E, F, E, T, F, E, T, E, E, E, E, F]), ([E, T, E, E, E, F, E, F, T, T, E, E, E, E, F], [E, T, E, E, F, E, E, F, T, T, E, E, E, E, F]), ([E, T, E, E, E, F, T, F, E, E, T, E, E, E, F], [E, T, E, E, F, E, T, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1385 (And.intro z_1456 (And.intro z_1457 trivial)))

theorem z_1459 : le (tf [F, E, E, T, E, E, F, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, T, E, E, E, E, E, F, T] [([F, E, E, E, T, E, F, T, E, E, E, E, E, F, T], [F, E, E, E, T, E, F, T, E, E, E, E, F, E, T]), ([F, E, E, T, E, E, F, E, T, E, E, E, E, F, T], [F, E, E, T, E, F, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1224 (And.intro z_1172 trivial))

theorem z_1460 : le (tf [E, F, E, T, E, T, F, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, F, E, E, E, E, E, E, F, T] [([E, F, E, E, T, T, F, E, E, E, E, E, E, F, T], [E, F, E, E, T, T, F, E, E, E, E, E, F, E, T]), ([E, F, E, T, E, E, F, T, E, E, E, E, E, F, T], [F, E, E, T, E, E, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1226 (And.intro z_1459 trivial))

theorem z_1461 : le (tf [F, E, E, T, F, E, E, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, T, F, E, E, T, E, E, E, E, E, F, T] [([F, E, E, E, F, T, E, T, E, E, E, E, E, F, T], [F, E, E, E, F, T, E, T, E, E, E, E, F, E, T]), ([F, E, E, T, F, E, E, E, T, E, E, E, E, F, T], [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_918 trivial))

theorem z_1462 : le (tf [F, E, T, E, F, E, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, F, E, E, E, T, E, E, E, E, F, T] [([F, E, E, T, F, E, E, E, T, E, E, E, E, F, T], [F, E, E, T, F, E, E, E, T, E, E, E, F, E, T]), ([F, E, T, E, F, E, E, E, E, T, E, E, E, F, T], [F, E, T, E, F, E, E, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_918 (And.intro z_920 trivial))

theorem z_1463 : le (tf [F, E, T, E, E, F, E, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, T, E, E, E, E, E, F, T] [([F, E, E, T, E, F, E, T, E, E, E, E, E, F, T], [F, E, E, T, F, E, E, T, E, E, E, E, E, F, T]), ([F, E, T, E, E, F, E, E, T, E, E, E, E, F, T], [F, E, T, E, F, E, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1461 (And.intro z_1462 trivial))

theorem z_1464 : le (tf [F, T, E, E, F, E, E, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, E, T, E, F, E, T] [([F, E, T, E, F, E, E, E, E, E, T, E, F, E, T], [F, E, T, E, F, E, E, E, E, E, T, F, E, E, T]), ([F, T, E, E, F, E, E, E, E, E, E, T, F, E, T], [F, T, E, F, E, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_902 (And.intro z_1062 trivial))

theorem z_1465 : le (tf [F, T, E, E, F, E, E, E, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, F, E, E, E, E, T, E, E, E, F, T] [([F, E, T, E, F, E, E, E, E, T, E, E, E, F, T], [F, E, T, E, F, E, E, E, E, T, E, E, F, E, T]), ([F, T, E, E, F, E, E, E, E, E, T, E, E, F, T], [F, T, E, E, F, E, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_920 (And.intro z_1464 trivial))

theorem z_1466 : le (tf [F, T, E, E, E, F, E, E, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, T, E, E, E, E, F, T] [([F, E, T, E, E, F, E, E, T, E, E, E, E, F, T], [F, E, T, E, F, E, E, E, T, E, E, E, E, F, T]), ([F, T, E, E, E, F, E, E, E, T, E, E, E, F, T], [F, T, E, E, F, E, E, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1462 (And.intro z_1465 trivial))

theorem z_1467 : le (tf [F, T, E, E, E, E, F, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, T, E, E, E, E, E, F, T] [([F, E, T, E, E, E, F, T, E, E, E, E, E, F, T], [F, E, T, E, E, F, E, T, E, E, E, E, E, F, T]), ([F, T, E, E, E, E, F, E, T, E, E, E, E, F, T], [F, T, E, E, E, F, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1463 (And.intro z_1466 trivial))

theorem z_1468 : le (tf [E, T, F, E, E, T, F, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, E, E, E, E, E, F, T] [([E, E, F, T, E, T, F, E, E, E, E, E, E, F, T], [E, F, E, T, E, T, F, E, E, E, E, E, E, F, T]), ([E, T, F, E, E, E, F, T, E, E, E, E, E, F, T], [F, T, E, E, E, E, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1460 (And.intro z_1467 trivial))

theorem z_1469 : le (tf [E, T, E, F, T, E, F, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, E, F, T, E, F, E, E, E, E, E, E, F, T] [([E, E, T, F, T, E, F, E, E, E, E, E, E, F, T], [E, F, T, E, T, E, F, E, E, E, E, E, E, F, T]), ([E, T, E, F, E, T, F, E, E, E, E, E, E, F, T], [E, T, F, E, E, T, F, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1449 (And.intro z_1468 trivial))

theorem z_1470 : le (tf [E, T, E, E, T, F, F, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, F, E, E, E, E, E, T, F, E] [([E, E, T, E, T, F, F, E, E, E, E, E, T, F, E], [E, E, T, F, T, E, F, E, E, E, E, E, T, F, E]), ([E, T, E, E, T, F, F, E, E, E, E, E, E, F, T], [E, T, E, F, T, E, F, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1450 (And.intro z_1469 trivial))

theorem z_1471 : le (tf [E, T, E, E, T, F, F, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, F, E, E, E, E, T, E, E, F] [([E, E, T, E, T, F, F, E, E, E, E, T, E, E, F], [E, E, T, E, T, F, F, E, E, E, E, T, E, F, E]), ([E, T, E, E, T, F, F, E, E, E, E, E, T, E, F], [E, T, E, E, T, F, F, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1451 (And.intro z_1470 trivial))

theorem z_1472 : le (tf [E, T, E, E, T, F, E, F, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, F, E, E, T, E, E, E, F] [([E, E, T, E, T, F, E, F, E, E, T, E, E, E, F], [E, E, T, E, T, F, F, E, E, E, T, E, E, E, F]), ([E, T, E, E, E, F, T, F, E, E, T, E, E, E, F], [E, T, E, E, F, E, T, F, E, E, T, E, E, E, F]), ([E, T, E, E, T, F, E, F, E, E, E, T, E, E, F], [E, T, E, E, T, F, F, E, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1452 (And.intro z_1457 (And.intro z_1471 trivial)))

theorem z_1473 : le (tf [E, T, E, E, T, F, E, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, F, T, E, E, E, E, F] [([E, E, T, E, T, F, E, E, F, T, E, E, E, E, F], [E, E, T, E, T, F, E, F, E, T, E, E, E, E, F]), ([E, T, E, E, E, F, T, E, F, T, E, E, E, E, F], [E, T, E, E, E, F, T, F, E, T, E, E, E, E, F]), ([E, T, E, E, T, F, E, E, F, E, T, E, E, E, F], [E, T, E, E, T, F, E, F, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1453 (And.intro z_1458 (And.intro z_1472 trivial)))

theorem z_1474 : le (tf [E, T, E, E, T, F, E, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, T, E, F, E, E, E, F] [([E, E, T, E, T, F, E, E, T, E, F, E, E, E, F], [E, E, T, E, T, F, E, E, T, F, E, E, E, E, F]), ([E, T, E, E, E, F, T, E, T, E, F, E, E, E, F], [E, T, E, E, E, F, T, E, T, F, E, E, E, E, F]), ([E, T, E, E, T, F, E, E, E, T, F, E, E, E, F], [E, T, E, E, T, F, E, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1407 (And.intro z_1411 (And.intro z_1473 trivial)))

theorem z_1475 : le (tf [E, T, E, E, T, F, E, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, T, E, E, E, F, E, E, F] [([E, E, T, E, T, F, E, T, E, E, E, F, E, E, F], [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F]), ([E, T, E, E, E, F, T, T, E, E, E, F, E, E, F], [E, T, E, E, E, F, T, T, E, E, F, E, E, E, F]), ([E, T, E, E, T, F, E, E, T, E, E, F, E, E, F], [E, T, E, E, T, F, E, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1408 (And.intro z_1412 (And.intro z_1474 trivial)))

theorem z_1476 : le (tf [E, T, E, E, T, F, T, E, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, T, E, E, E, E, E, F, E, F] [([E, E, T, E, T, F, T, E, E, E, E, E, F, E, F], [E, E, T, E, T, F, T, E, E, E, E, F, E, E, F]), ([E, T, E, E, T, F, E, T, E, E, E, E, F, E, F], [E, T, E, E, T, F, E, T, E, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1409 (And.intro z_1475 trivial))

theorem z_1477 : le (tf [E, F, E, T, E, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, E, F, E, T, E, F] [([E, F, E, E, T, T, E, E, E, E, F, E, T, E, F], [F, E, E, E, T, T, E, E, E, E, F, E, T, E, F]), ([E, F, E, T, E, E, T, E, E, E, F, E, T, E, F], [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F]), ([E, F, E, T, E, T, E, E, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_995 (And.intro z_963 (And.intro z_996 trivial)))

theorem z_1478 : le (tf [E, F, E, T, E, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, F, E, E, E, T, F] [([E, F, E, E, T, T, E, E, E, F, E, E, E, T, F], [F, E, E, E, T, T, E, E, E, F, E, E, E, T, F]), ([E, F, E, T, E, E, T, E, E, F, E, E, E, T, F], [F, E, E, T, E, E, T, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_968 (And.intro z_962 trivial))

theorem z_1479 : le (tf [E, T, F, E, E, T, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, F, E, E, E, T, F] [([E, E, F, T, E, T, E, E, E, F, E, E, E, T, F], [E, F, E, T, E, T, E, E, E, F, E, E, E, T, F]), ([E, T, F, E, E, E, T, E, E, F, E, E, E, T, F], [E, T, F, E, E, E, T, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1478 (And.intro z_1126 trivial))

theorem z_1480 : le (tf [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F] [([E, E, F, T, E, T, E, E, E, E, F, E, T, E, F], [E, F, E, T, E, T, E, E, E, E, F, E, T, E, F]), ([E, T, F, E, E, E, T, E, E, E, F, E, T, E, F], [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F]), ([E, T, F, E, E, T, E, E, E, E, F, E, E, T, F], [E, T, F, E, E, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1477 (And.intro z_1127 (And.intro z_1479 trivial)))

theorem z_1481 : le (tf [E, T, E, F, E, T, E, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, E, E, F, T, E, E, F] [([E, E, T, F, E, T, E, E, E, E, F, T, E, E, F], [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F]), ([E, T, E, F, E, E, T, E, E, E, F, T, E, E, F], [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F]), ([E, T, E, F, E, T, E, E, E, E, F, E, T, E, F], [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_977 (And.intro z_1128 (And.intro z_1480 trivial)))

theorem z_1482 : le (tf [E, T, F, T, E, E, E, E, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, E, E, F, E, E, E, T, F] [([E, T, F, E, T, E, E, E, E, F, E, E, E, T, F], [E, T, F, E, T, E, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1274 trivial)

theorem z_1483 : le (tf [E, T, F, T, E, E, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, E, E, E, F, E, T, E, F] [([E, T, F, E, T, E, E, E, E, E, F, E, T, E, F], [E, T, F, E, T, E, E, E, E, F, E, E, T, E, F]), ([E, T, F, T, E, E, E, E, E, E, F, E, E, T, F], [E, T, F, T, E, E, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1275 (And.intro z_1482 trivial))

theorem z_1484 : le (tf [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F] [([E, E, T, T, F, E, E, E, E, E, F, T, E, E, F], [E, E, T, T, F, E, E, E, E, F, E, T, E, E, F]), ([E, T, E, E, F, T, E, E, E, E, F, T, E, E, F], [E, T, E, F, E, T, E, E, E, E, F, T, E, E, F]), ([E, T, E, T, F, E, E, E, E, E, F, E, T, E, F], [E, T, F, T, E, E, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1394 (And.intro z_1481 (And.intro z_1483 trivial)))

theorem z_1485 : le (tf [E, T, E, T, E, F, E, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, E, E, T, F, E, E, E, F] [([E, E, T, T, E, F, E, E, E, T, F, E, E, E, F], [E, E, T, T, F, E, E, E, E, T, F, E, E, E, F]), ([E, T, E, E, T, F, E, E, E, T, F, E, E, E, F], [E, T, E, E, T, F, E, E, F, T, E, E, E, E, F]), ([E, T, E, T, E, F, E, E, E, E, F, T, E, E, F], [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1395 (And.intro z_1473 (And.intro z_1484 trivial)))

theorem z_1486 : le (tf [E, T, E, T, E, F, E, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, E, T, E, E, F, E, E, F] [([E, E, T, T, E, F, E, E, T, E, E, F, E, E, F], [E, E, T, T, F, E, E, E, T, E, E, F, E, E, F]), ([E, T, E, E, T, F, E, E, T, E, E, F, E, E, F], [E, T, E, E, T, F, E, E, T, E, F, E, E, E, F]), ([E, T, E, T, E, F, E, E, E, T, E, F, E, E, F], [E, T, E, T, E, F, E, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1396 (And.intro z_1474 (And.intro z_1485 trivial)))

theorem z_1487 : le (tf [E, T, E, T, E, F, E, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, T, E, E, E, E, F, E, F] [([E, E, T, T, E, F, E, T, E, E, E, E, F, E, F], [E, E, T, T, F, E, E, T, E, E, E, E, F, E, F]), ([E, T, E, E, T, F, E, T, E, E, E, E, F, E, F], [E, T, E, E, T, F, E, T, E, E, E, F, E, E, F]), ([E, T, E, T, E, F, E, E, T, E, E, E, F, E, F], [E, T, E, T, E, F, E, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1397 (And.intro z_1475 (And.intro z_1486 trivial)))

theorem z_1488 : le (tf [E, T, E, T, E, F, T, E, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, T, E, E, E, E, E, E, F, F] [([E, E, T, T, E, F, T, E, E, E, E, E, E, F, F], [E, E, T, T, F, E, T, E, E, E, E, E, E, F, F]), ([E, T, E, E, T, F, T, E, E, E, E, E, E, F, F], [E, T, E, E, T, F, T, E, E, E, E, E, F, E, F]), ([E, T, E, T, E, F, E, T, E, E, E, E, E, F, F], [E, T, E, T, E, F, E, T, E, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1398 (And.intro z_1476 (And.intro z_1487 trivial)))

theorem z_1489 : le (tf [E, T, E, T, E, T, E, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, T, E, F, E, E, E, E, E, F, F] [([E, E, T, T, E, T, E, F, E, E, E, E, E, F, F], [E, E, T, T, E, T, F, E, E, E, E, E, E, F, F]), ([E, T, E, E, T, T, E, F, E, E, E, E, E, F, F], [E, T, E, E, T, T, F, E, E, E, E, E, E, F, F]), ([E, T, E, T, E, E, T, F, E, E, E, E, E, F, F], [E, T, E, T, E, F, T, E, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1017 (And.intro z_1281 (And.intro z_1488 trivial)))

theorem z_1490 : le (tf [E, T, E, T, T, E, E, E, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, T, E, E, E, F, E, E, E, E, F, F] [([E, E, T, T, T, E, E, E, F, E, E, E, E, F, F], [E, E, T, T, T, E, E, F, E, E, E, E, E, F, F]), ([E, T, E, T, E, T, E, E, F, E, E, E, E, F, F], [E, T, E, T, E, T, E, F, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1018 (And.intro z_1489 trivial))

theorem z_1491 : le (tf [F, E, E, T, E, T, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, E, E, E, T, E, F, F] [([F, E, E, E, T, T, E, E, E, E, E, T, E, F, F], [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F]), ([F, E, E, T, E, E, T, E, E, E, E, T, E, F, F], [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F]), ([F, E, E, T, E, T, E, E, E, E, E, E, T, F, F], [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_987 (And.intro z_1097 (And.intro z_997 trivial)))

theorem z_1492 : le (tf [E, F, E, T, E, T, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, E, T, E, E, F, F] [([E, F, E, E, T, T, E, E, E, E, T, E, E, F, F], [F, E, E, E, T, T, E, E, E, E, T, E, E, F, F]), ([E, F, E, T, E, E, T, E, E, E, T, E, E, F, F], [E, F, E, T, E, E, T, E, E, E, T, E, F, E, F]), ([E, F, E, T, E, T, E, E, E, E, E, T, E, F, F], [F, E, E, T, E, T, E, E, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_988 (And.intro z_1098 (And.intro z_1491 trivial)))

theorem z_1493 : le (tf [F, E, E, T, E, T, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, T, E, E, E, E, E, E, F, T, F] [([F, E, E, E, T, T, E, E, E, E, E, E, F, T, F], [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F]), ([F, E, E, T, E, E, T, E, E, E, E, E, F, T, F], [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_986 (And.intro z_1096 trivial))

theorem z_1494 : le (tf [E, F, E, T, E, T, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, E, E, T, F, E, F] [([E, F, E, E, T, T, E, E, E, E, E, T, F, E, F], [F, E, E, E, T, T, E, E, E, E, E, T, F, E, F]), ([E, F, E, T, E, E, T, E, E, E, E, T, F, E, F], [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F]), ([E, F, E, T, E, T, E, E, E, E, E, E, F, T, F], [F, E, E, T, E, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_987 (And.intro z_1097 (And.intro z_1493 trivial)))

theorem z_1495 : le (tf [F, T, E, E, E, T, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [F, T, E, E, E, T, E, E, E, E, E, E, F, T, F] [([F, E, T, E, E, T, E, E, E, E, E, E, F, T, F], [F, E, T, E, E, T, E, E, E, E, E, F, E, T, F]), ([F, T, E, E, E, E, T, E, E, E, E, E, F, T, F], [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_998 (And.intro z_1138 trivial))

theorem z_1496 : le (tf [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F] [([E, E, F, T, E, T, E, E, E, E, E, T, F, E, F], [E, F, E, T, E, T, E, E, E, E, E, T, F, E, F]), ([E, T, F, E, E, E, T, E, E, E, E, T, F, E, F], [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F]), ([E, T, F, E, E, T, E, E, E, E, E, E, F, T, F], [F, T, E, E, E, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1494 (And.intro z_1128 (And.intro z_1495 trivial)))

theorem z_1497 : le (tf [E, T, F, E, E, T, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, E, T, E, E, F, F] [([E, E, F, T, E, T, E, E, E, E, T, E, E, F, F], [E, F, E, T, E, T, E, E, E, E, T, E, E, F, F]), ([E, T, F, E, E, E, T, E, E, E, T, E, E, F, F], [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F]), ([E, T, F, E, E, T, E, E, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1492 (And.intro z_1129 (And.intro z_1496 trivial)))

theorem z_1498 : le (tf [E, T, E, F, E, T, E, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, E, T, E, E, E, F, F] [([E, E, T, F, E, T, E, E, E, T, E, E, E, F, F], [E, E, T, F, E, T, E, E, E, T, E, E, F, E, F]), ([E, T, E, F, E, E, T, E, E, T, E, E, E, F, F], [E, T, F, E, E, E, T, E, E, T, E, E, E, F, F]), ([E, T, E, F, E, T, E, E, E, E, T, E, E, F, F], [E, T, F, E, E, T, E, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1001 (And.intro z_1130 (And.intro z_1497 trivial)))

theorem z_1499 : le (tf [E, T, E, F, E, T, E, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, E, E, T, E, F, E, F] [([E, E, T, F, E, T, E, E, E, E, T, E, F, E, F], [E, E, T, F, E, T, E, E, E, E, T, F, E, E, F]), ([E, T, E, F, E, E, T, E, E, E, T, E, F, E, F], [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F]), ([E, T, E, F, E, T, E, E, E, E, E, T, F, E, F], [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1000 (And.intro z_1129 (And.intro z_1496 trivial)))

theorem z_1500 : le (tf [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F] [([E, E, T, T, F, E, E, E, E, E, T, E, F, E, F], [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F]), ([E, T, E, E, F, T, E, E, E, E, T, E, F, E, F], [E, T, E, F, E, T, E, E, E, E, T, E, F, E, F]), ([E, T, E, T, F, E, E, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1013 (And.intro z_1499 (And.intro z_1484 trivial)))

theorem z_1501 : le (tf [E, T, E, T, F, E, E, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, T, E, E, E, F, F] [([E, E, T, T, F, E, E, E, E, T, E, E, E, F, F], [E, E, T, T, F, E, E, E, E, T, E, E, F, E, F]), ([E, T, E, E, F, T, E, E, E, T, E, E, E, F, F], [E, T, E, F, E, T, E, E, E, T, E, E, E, F, F]), ([E, T, E, T, F, E, E, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1014 (And.intro z_1498 (And.intro z_1500 trivial)))

theorem z_1502 : le (tf [E, T, E, T, E, F, E, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, E, T, E, E, E, E, F, F] [([E, E, T, T, E, F, E, E, T, E, E, E, E, F, F], [E, E, T, T, F, E, E, E, T, E, E, E, E, F, F]), ([E, T, E, E, T, F, E, E, T, E, E, E, E, F, F], [E, T, E, E, T, F, E, E, T, E, E, E, F, E, F]), ([E, T, E, T, E, F, E, E, E, T, E, E, E, F, F], [E, T, E, T, F, E, E, E, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1015 (And.intro z_1279 (And.intro z_1501 trivial)))

theorem z_1503 : le (tf [F, E, E, T, T, E, E, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, E, E, E, E, E, T, F, F] [([F, E, E, T, E, T, E, E, E, E, E, E, T, F, F], [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_997 trivial)

theorem z_1504 : le (tf [E, F, E, T, T, E, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, E, E, T, E, F, F] [([E, F, E, T, E, T, E, E, E, E, E, T, E, F, F], [F, E, E, T, E, T, E, E, E, E, E, T, E, F, F]), ([E, F, E, T, T, E, E, E, E, E, E, E, T, F, F], [F, E, E, T, T, E, E, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1491 (And.intro z_1503 trivial))

theorem z_1505 : le (tf [F, E, E, T, T, E, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, T, T, E, E, E, E, E, E, F, E, T, F] [([F, E, E, T, E, T, E, E, E, E, E, F, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_996 trivial)

theorem z_1506 : le (tf [E, F, E, T, T, E, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, E, E, F, T, E, F] [([E, F, E, T, E, T, E, E, E, E, E, F, T, E, F], [F, E, E, T, E, T, E, E, E, E, E, F, T, E, F]), ([E, F, E, T, T, E, E, E, E, E, E, F, E, T, F], [F, E, E, T, T, E, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_997 (And.intro z_1505 trivial))

theorem z_1507 : le (tf [E, F, E, T, T, E, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, E, F, E, E, T, F] [([E, F, E, T, E, T, E, E, E, E, F, E, E, T, F], [F, E, E, T, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_996 trivial)

theorem z_1508 : le (tf [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F] [([E, E, F, T, T, E, E, E, E, E, F, E, E, T, F], [E, F, E, T, T, E, E, E, E, E, F, E, E, T, F]), ([E, T, F, E, E, T, E, E, E, E, F, E, E, T, F], [E, T, F, E, E, T, E, E, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1507 (And.intro z_1479 trivial))

theorem z_1509 : le (tf [E, T, F, E, T, E, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, E, E, F, T, E, F] [([E, E, F, T, T, E, E, E, E, E, E, F, T, E, F], [E, F, E, T, T, E, E, E, E, E, E, F, T, E, F]), ([E, T, F, E, E, T, E, E, E, E, E, F, T, E, F], [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F]), ([E, T, F, E, T, E, E, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1506 (And.intro z_1480 (And.intro z_1508 trivial)))

theorem z_1510 : le (tf [E, T, F, E, T, E, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, E, E, T, E, F, F] [([E, E, F, T, T, E, E, E, E, E, E, T, E, F, F], [E, F, E, T, T, E, E, E, E, E, E, T, E, F, F]), ([E, T, F, E, E, T, E, E, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F]), ([E, T, F, E, T, E, E, E, E, E, E, E, T, F, F], [E, T, F, E, T, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1504 (And.intro z_1496 (And.intro z_1509 trivial)))

theorem z_1511 : le (tf [E, T, T, F, E, E, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, E, F, E, E, T, F] [([E, T, E, F, T, E, E, E, E, E, F, E, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1508 trivial)

theorem z_1512 : le (tf [E, T, T, F, E, E, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, E, E, F, T, E, F] [([E, T, E, F, T, E, E, E, E, E, E, F, T, E, F], [E, T, F, E, T, E, E, E, E, E, E, F, T, E, F]), ([E, T, T, F, E, E, E, E, E, E, E, F, E, T, F], [E, T, T, F, E, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1509 (And.intro z_1511 trivial))

theorem z_1513 : le (tf [E, T, T, F, E, E, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, E, E, T, E, F, F] [([E, T, E, F, T, E, E, E, E, E, E, T, E, F, F], [E, T, F, E, T, E, E, E, E, E, E, T, E, F, F]), ([E, T, T, F, E, E, E, E, E, E, E, E, T, F, F], [E, T, T, F, E, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1510 (And.intro z_1512 trivial))

theorem z_1514 : le (tf [E, T, T, E, F, E, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, E, E, T, E, E, F, F] [([E, T, E, T, F, E, E, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F]), ([E, T, T, E, F, E, E, E, E, E, E, T, E, F, F], [E, T, T, F, E, E, E, E, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1500 (And.intro z_1513 trivial))

theorem z_1515 : le (tf [E, T, T, E, E, F, E, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, E, E, T, E, E, E, F, F] [([E, T, E, T, E, F, E, E, E, T, E, E, E, F, F], [E, T, E, T, F, E, E, E, E, T, E, E, E, F, F]), ([E, T, T, E, E, F, E, E, E, E, T, E, E, F, F], [E, T, T, E, F, E, E, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1501 (And.intro z_1514 trivial))

theorem z_1516 : le (tf [E, T, T, E, E, E, F, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, E, F, E, T, E, E, E, E, F, F] [([E, T, E, T, E, E, F, E, T, E, E, E, E, F, F], [E, T, E, T, E, F, E, E, T, E, E, E, E, F, F]), ([E, T, T, E, E, E, F, E, E, T, E, E, E, F, F], [E, T, T, E, E, F, E, E, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1502 (And.intro z_1515 trivial))

theorem z_1517 : le (tf [E, T, T, E, E, E, T, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, E, T, F, E, E, E, E, E, F, F] [([E, T, E, T, E, E, T, F, E, E, E, E, E, F, F], [E, T, E, T, E, F, T, E, E, E, E, E, E, F, F]), ([E, T, T, E, E, E, E, F, T, E, E, E, E, F, F], [E, T, T, E, E, E, F, E, T, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1488 (And.intro z_1516 trivial))

theorem z_1518 : le (tf [E, T, T, E, E, T, E, E, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, T, E, E, F, E, E, E, E, F, F] [([E, T, E, T, E, T, E, E, F, E, E, E, E, F, F], [E, T, E, T, E, T, E, F, E, E, E, E, E, F, F]), ([E, T, T, E, E, E, T, E, F, E, E, E, E, F, F], [E, T, T, E, E, E, T, F, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1489 (And.intro z_1517 trivial))

theorem z_1519 : le (tf [E, T, T, E, T, E, E, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, E, T, E, E, E, E, F, E, E, E, F, F] [([E, T, E, T, T, E, E, E, E, F, E, E, E, F, F], [E, T, E, T, T, E, E, E, F, E, E, E, E, F, F]), ([E, T, T, E, E, T, E, E, E, F, E, E, E, F, F], [E, T, T, E, E, T, E, E, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1490 (And.intro z_1518 trivial))

theorem z_1520 : le (tf [E, T, T, T, E, E, E, E, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [E, T, T, T, E, E, E, E, E, E, F, E, E, F, F] [([E, T, T, E, T, E, E, E, E, E, F, E, E, F, F], [E, T, T, E, T, E, E, E, E, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1519 trivial)

theorem z_1521 : le (tf [E, E, E, E, T, T, T, F, F, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, T, F, F, E, E, E, E, F, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1522 : le (tf [E, E, E, T, E, T, T, F, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, E, T, T, F, F, E, E, E, E, E, F] [([E, E, E, E, T, T, T, F, F, E, E, E, E, E, F], [E, E, E, E, T, T, T, F, F, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1521 trivial)

theorem z_1523 : le (tf [F, E, E, E, T, E, E, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, E, F, T, T, E, E, F] [([F, E, E, E, E, T, E, E, E, F, T, T, E, E, F], [F, E, E, E, E, T, E, E, F, E, T, T, E, E, F]), ([F, E, E, E, T, E, E, E, E, F, T, E, T, E, F], [F, E, E, E, T, E, E, E, F, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_207 (And.intro z_781 trivial))

theorem z_1524 : le (tf [E, F, E, E, T, E, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, T, F, E, T, E, E, F] [([E, F, E, E, E, T, E, E, T, F, E, T, E, E, F], [F, E, E, E, E, T, E, E, T, F, E, T, E, E, F]), ([E, F, E, E, T, E, E, E, E, F, T, T, E, E, F], [F, E, E, E, T, E, E, E, E, F, T, T, E, E, F]), ([E, F, E, E, T, E, E, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_250 (And.intro z_1523 (And.intro z_783 trivial)))

theorem z_1525 : le (tf [E, E, F, E, T, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, T, F, T, E, E, E, F] [([E, E, F, E, E, T, E, E, T, F, T, E, E, E, F], [E, F, E, E, E, T, E, E, T, F, T, E, E, E, F]), ([E, E, F, E, T, E, E, E, T, F, E, T, E, E, F], [E, F, E, E, T, E, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_458 (And.intro z_1524 trivial))

theorem z_1526 : le (tf [F, E, E, E, E, E, F, T, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, E, T, T, E, F, E] [([F, E, E, E, E, E, F, E, T, E, T, T, E, F, E], [F, E, E, E, E, F, E, E, T, E, T, T, E, F, E]), ([F, E, E, E, E, E, F, T, E, E, T, E, T, F, E], [F, E, E, E, E, F, E, T, E, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_938 trivial))

theorem z_1527 : le (tf [E, F, E, E, E, T, F, E, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, E, T, T, E, F, E] [([E, F, E, E, E, E, F, T, E, E, T, T, E, F, E], [F, E, E, E, E, E, F, T, E, E, T, T, E, F, E]), ([E, F, E, E, E, T, F, E, E, E, T, E, T, F, E], [E, F, E, E, E, T, F, E, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1526 (And.intro z_940 trivial))

theorem z_1528 : le (tf [E, F, E, E, T, E, F, E, E, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, E, T, T, E, E, F] [([E, F, E, E, E, T, F, E, E, E, T, T, E, E, F], [E, F, E, E, E, T, F, E, E, E, T, T, E, F, E]), ([E, F, E, E, T, E, F, E, E, E, T, E, T, E, F], [E, F, E, E, T, F, E, E, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1527 (And.intro z_944 trivial))

theorem z_1529 : le (tf [E, F, E, T, E, E, E, F, E, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, E, T, T, E, E, F] [([E, F, E, E, T, E, E, F, E, E, T, T, E, E, F], [E, F, E, E, T, E, F, E, E, E, T, T, E, E, F]), ([E, F, E, T, E, E, E, F, E, E, T, E, T, E, F], [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1528 (And.intro z_1101 trivial))

theorem z_1530 : le (tf [E, F, T, E, E, E, E, F, E, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, E, E, T, E, T, E, F] [([E, F, E, T, E, E, E, F, E, E, T, E, T, E, F], [E, F, E, T, E, E, F, E, E, E, T, E, T, E, F]), ([E, F, T, E, E, E, E, F, E, E, E, T, T, E, F], [F, E, T, E, E, E, E, F, E, E, E, T, T, E, F]), ([E, F, T, E, E, E, E, F, E, E, T, E, E, T, F], [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1101 (And.intro z_1080 (And.intro z_1085 trivial)))

theorem z_1531 : le (tf [E, F, T, E, E, E, E, E, F, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, F, E, T, T, E, E, F] [([E, F, E, T, E, E, E, E, F, E, T, T, E, E, F], [E, F, E, T, E, E, E, F, E, E, T, T, E, E, F]), ([E, F, T, E, E, E, E, E, F, E, T, E, T, E, F], [E, F, T, E, E, E, E, F, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1529 (And.intro z_1530 trivial))

theorem z_1532 : le (tf [E, F, T, E, E, E, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, T, F, E, T, E, E, F] [([E, F, E, T, E, E, E, E, T, F, E, T, E, E, F], [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F]), ([E, F, T, E, E, E, E, E, E, F, T, T, E, E, F], [E, F, T, E, E, E, E, E, F, E, T, T, E, E, F]), ([E, F, T, E, E, E, E, E, T, F, E, E, T, E, F], [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_526 (And.intro z_1531 (And.intro z_951 trivial)))

theorem z_1533 : le (tf [E, E, T, F, E, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, T, F, T, E, E, E, F] [([E, E, E, F, T, E, E, E, T, F, T, E, E, E, F], [E, E, F, E, T, E, E, E, T, F, T, E, E, E, F]), ([E, E, T, F, E, E, E, E, T, F, E, T, E, E, F], [E, F, T, E, E, E, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1525 (And.intro z_1532 trivial))

theorem z_1534 : le (tf [E, F, E, E, T, E, E, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, F, E, E, T, E, F] [([E, F, E, E, E, T, E, T, E, F, E, E, T, E, F], [F, E, E, E, E, T, E, T, E, F, E, E, T, E, F]), ([E, F, E, E, T, E, E, E, T, F, E, E, T, E, F], [F, E, E, E, T, E, E, E, T, F, E, E, T, E, F]), ([E, F, E, E, T, E, E, T, E, F, E, E, E, T, F], [F, E, E, E, T, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_440 (And.intro z_783 (And.intro z_784 trivial)))

theorem z_1535 : le (tf [E, E, F, E, T, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, E, F, E, T, E, E, F] [([E, E, F, E, E, T, E, T, E, F, E, T, E, E, F], [E, F, E, E, E, T, E, T, E, F, E, T, E, E, F]), ([E, E, F, E, T, E, E, E, T, F, E, T, E, E, F], [E, F, E, E, T, E, E, E, T, F, E, T, E, E, F]), ([E, E, F, E, T, E, E, T, E, F, E, E, T, E, F], [E, F, E, E, T, E, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_459 (And.intro z_1524 (And.intro z_1534 trivial)))

theorem z_1536 : le (tf [E, F, T, E, E, E, E, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, T, E, F, E, E, T, E, F] [([E, F, E, T, E, E, E, T, E, F, E, E, T, E, F], [F, E, E, T, E, E, E, T, E, F, E, E, T, E, F]), ([E, F, T, E, E, E, E, E, T, F, E, E, T, E, F], [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F]), ([E, F, T, E, E, E, E, T, E, F, E, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_537 (And.intro z_951 (And.intro z_854 trivial)))

theorem z_1537 : le (tf [E, E, T, F, E, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, E, F, E, T, E, E, F] [([E, E, E, F, T, E, E, T, E, F, E, T, E, E, F], [E, E, F, E, T, E, E, T, E, F, E, T, E, E, F]), ([E, E, T, F, E, E, E, E, T, F, E, T, E, E, F], [E, F, T, E, E, E, E, E, T, F, E, T, E, E, F]), ([E, E, T, F, E, E, E, T, E, F, E, E, T, E, F], [E, F, T, E, E, E, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1535 (And.intro z_1532 (And.intro z_1536 trivial)))

theorem z_1538 : le (tf [E, E, T, E, F, E, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, T, E, F, T, E, E, E, F] [([E, E, E, T, F, E, E, T, E, F, T, E, E, E, F], [E, E, F, T, E, E, E, T, E, F, T, E, E, E, F]), ([E, E, T, E, F, E, E, E, T, F, T, E, E, E, F], [E, E, T, F, E, E, E, E, T, F, T, E, E, E, F]), ([E, E, T, E, F, E, E, T, E, F, E, T, E, E, F], [E, E, T, F, E, E, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_539 (And.intro z_1533 (And.intro z_1537 trivial)))

theorem z_1539 : le (tf [E, E, T, E, E, F, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, F, E, T, T, F, E, E, E, E, F] [([E, E, E, T, E, F, E, T, T, F, E, E, E, E, F], [E, E, E, T, F, E, E, T, T, F, E, E, E, E, F]), ([E, E, T, E, E, F, E, T, E, F, T, E, E, E, F], [E, E, T, E, F, E, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_540 (And.intro z_1538 trivial))

theorem z_1540 : le (tf [E, E, T, E, F, T, E, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, E, E, E, F, T, E, E, E, F] [([E, E, E, T, F, T, E, E, E, F, T, E, E, E, F], [E, E, E, T, F, T, E, E, F, E, T, E, E, E, F]), ([E, E, T, E, F, E, T, E, E, F, T, E, E, E, F], [E, E, T, F, E, E, T, E, E, F, T, E, E, E, F]), ([E, E, T, E, F, T, E, E, E, F, E, T, E, E, F], [E, E, T, F, E, T, E, E, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1368 (And.intro z_955 (And.intro z_977 trivial)))

theorem z_1541 : le (tf [E, E, T, E, E, T, F, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, F, E, T, F, E, E, E, E, F] [([E, E, E, T, E, T, F, E, T, F, E, E, E, E, F], [E, E, E, T, F, T, E, E, T, F, E, E, E, E, F]), ([E, E, T, E, E, E, F, T, T, F, E, E, E, E, F], [E, E, T, E, E, F, E, T, T, F, E, E, E, E, F]), ([E, E, T, E, E, T, F, E, E, F, T, E, E, E, F], [E, E, T, E, F, T, E, E, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1369 (And.intro z_1539 (And.intro z_1540 trivial)))

theorem z_1542 : le (tf [E, E, T, E, E, T, T, F, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, T, F, E, F, E, E, E, E, F] [([E, E, E, T, E, T, T, F, E, F, E, E, E, E, F], [E, E, E, T, E, T, T, F, F, E, E, E, E, E, F]), ([E, E, T, E, E, T, E, F, T, F, E, E, E, E, F], [E, E, T, E, E, T, F, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1522 (And.intro z_1541 trivial))

theorem z_1543 : le (tf [F, E, E, T, E, E, E, E, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, E, T, F, T, E, E, F] [([F, E, E, E, T, E, E, E, E, T, F, T, E, E, F], [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F]), ([F, E, E, T, E, E, E, E, E, T, F, E, T, E, F], [F, E, E, T, E, E, E, E, E, T, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_798 (And.intro z_1025 trivial))

theorem z_1544 : le (tf [E, F, E, T, E, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, T, E, F, T, E, E, F] [([E, F, E, E, T, E, E, E, T, E, F, T, E, E, F], [F, E, E, E, T, E, E, E, T, E, F, T, E, E, F]), ([E, F, E, T, E, E, E, E, E, T, F, T, E, E, F], [F, E, E, T, E, E, E, E, E, T, F, T, E, E, F]), ([E, F, E, T, E, E, E, E, T, E, F, E, T, E, F], [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_799 (And.intro z_1543 (And.intro z_1031 trivial)))

theorem z_1545 : le (tf [E, F, E, T, E, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, T, E, T, E, E, F] [([E, F, E, E, T, E, E, E, F, T, E, T, E, E, F], [F, E, E, E, T, E, E, E, F, T, E, T, E, E, F]), ([E, F, E, T, E, E, E, E, F, E, T, T, E, E, F], [E, F, E, T, E, E, E, F, E, E, T, T, E, E, F]), ([E, F, E, T, E, E, E, E, F, T, E, E, T, E, F], [E, F, E, T, E, E, E, F, E, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_798 (And.intro z_1529 (And.intro z_1102 trivial)))

theorem z_1546 : le (tf [E, T, F, E, E, E, E, F, E, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, E, E, T, T, E, E, F] [([E, E, F, T, E, E, E, F, E, E, T, T, E, E, F], [E, F, E, T, E, E, E, F, E, E, T, T, E, E, F]), ([E, T, F, E, E, E, E, F, E, E, T, E, T, E, F], [E, T, F, E, E, E, F, E, E, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1529 (And.intro z_1117 trivial))

theorem z_1547 : le (tf [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F] [([E, E, F, T, E, E, E, E, F, T, E, T, E, E, F], [E, F, E, T, E, E, E, E, F, T, E, T, E, E, F]), ([E, T, F, E, E, E, E, E, F, E, T, T, E, E, F], [E, T, F, E, E, E, E, F, E, E, T, T, E, E, F]), ([E, T, F, E, E, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, E, E, F, E, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1545 (And.intro z_1546 (And.intro z_1119 trivial)))

theorem z_1548 : le (tf [E, T, F, E, E, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, T, E, F, T, E, E, F] [([E, E, F, T, E, E, E, E, T, E, F, T, E, E, F], [E, F, E, T, E, E, E, E, T, E, F, T, E, E, F]), ([E, T, F, E, E, E, E, E, E, T, F, T, E, E, F], [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F]), ([E, T, F, E, E, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1544 (And.intro z_1547 (And.intro z_1089 trivial)))

theorem z_1549 : le (tf [E, T, E, F, E, E, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, E, T, T, F, E, E, E, F] [([E, E, T, F, E, E, E, E, T, T, F, E, E, E, F], [E, E, T, F, E, E, E, E, T, T, F, E, E, F, E]), ([E, T, E, F, E, E, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_848 (And.intro z_1548 trivial))

theorem z_1550 : le (tf [E, T, E, F, E, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, E, E, F, T, E, E, F] [([E, E, T, F, E, E, E, T, E, E, F, T, E, E, F], [E, F, T, E, E, E, E, T, E, E, F, T, E, E, F]), ([E, T, E, F, E, E, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, E, E, T, E, F, T, E, E, F]), ([E, T, E, F, E, E, E, T, E, E, F, E, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_856 (And.intro z_1548 (And.intro z_1091 trivial)))

theorem z_1551 : le (tf [E, T, E, E, F, E, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, T, E, T, F, E, E, E, F] [([E, E, T, E, F, E, E, T, E, T, F, E, E, E, F], [E, E, T, F, E, E, E, T, E, T, F, E, E, E, F]), ([E, T, E, E, F, E, E, E, T, T, F, E, E, E, F], [E, T, E, F, E, E, E, E, T, T, F, E, E, E, F]), ([E, T, E, E, F, E, E, T, E, E, F, T, E, E, F], [E, T, E, F, E, E, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_857 (And.intro z_1549 (And.intro z_1550 trivial)))

theorem z_1552 : le (tf [E, T, E, E, E, F, E, T, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, E, T, T, E, F, E, E, E, F] [([E, E, T, E, E, F, E, T, T, E, F, E, E, E, F], [E, E, T, E, E, F, E, T, T, F, E, E, E, E, F]), ([E, T, E, E, E, F, E, T, E, T, F, E, E, E, F], [E, T, E, E, F, E, E, T, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1539 (And.intro z_1551 trivial))

theorem z_1553 : le (tf [E, E, T, E, F, E, E, T, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, T, F, T, E, E, E, E, F] [([E, E, E, T, F, E, E, T, F, T, E, E, E, E, F], [E, E, E, T, F, E, E, T, F, T, E, E, E, F, E]), ([E, E, T, E, F, E, E, T, F, E, T, E, E, E, F], [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_729 (And.intro z_935 trivial))

theorem z_1554 : le (tf [E, T, E, F, E, E, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, E, F, T, T, E, E, E, F] [([E, E, T, F, E, E, E, E, F, T, T, E, E, E, F], [E, F, T, E, E, E, E, E, F, T, T, E, E, E, F]), ([E, T, E, F, E, E, E, E, F, T, E, T, E, E, F], [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_870 (And.intro z_1547 trivial))

theorem z_1555 : le (tf [E, T, E, F, E, E, E, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, F, E, E, T, E, E, F] [([E, E, T, F, E, E, E, T, F, E, E, T, E, E, F], [E, E, T, F, E, E, F, T, E, E, E, T, E, E, F]), ([E, T, E, F, E, E, E, E, F, T, E, T, E, E, F], [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F]), ([E, T, E, F, E, E, E, T, F, E, E, E, T, E, F], [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_934 (And.intro z_1547 (And.intro z_1122 trivial)))

theorem z_1556 : le (tf [E, T, E, E, F, E, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, T, F, E, T, E, E, E, F] [([E, E, T, E, F, E, E, T, F, E, T, E, E, E, F], [E, E, T, F, E, E, E, T, F, E, T, E, E, E, F]), ([E, T, E, E, F, E, E, E, F, T, T, E, E, E, F], [E, T, E, F, E, E, E, E, F, T, T, E, E, E, F]), ([E, T, E, E, F, E, E, T, F, E, E, T, E, E, F], [E, T, E, F, E, E, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_935 (And.intro z_1554 (And.intro z_1555 trivial)))

theorem z_1557 : le (tf [E, T, E, E, E, F, E, T, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, E, T, F, T, E, E, E, E, F] [([E, E, T, E, E, F, E, T, F, T, E, E, E, E, F], [E, E, T, E, F, E, E, T, F, T, E, E, E, E, F]), ([E, T, E, E, E, F, E, T, F, E, T, E, E, E, F], [E, T, E, E, F, E, E, T, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1553 (And.intro z_1556 trivial))

theorem z_1558 : le (tf [E, T, E, E, F, T, E, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, T, E, E, F, E, T, E, E, E, F] [([E, E, T, E, F, T, E, E, F, E, T, E, E, E, F], [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F]), ([E, T, E, E, F, E, T, E, F, E, T, E, E, E, F], [E, T, E, E, F, E, T, F, E, E, T, E, E, E, F]), ([E, T, E, E, F, T, E, E, F, E, E, T, E, E, F], [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1241 (And.intro z_1457 (And.intro z_1271 trivial)))

theorem z_1559 : le (tf [E, T, E, E, E, T, F, E, F, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, F, E, F, T, E, E, E, E, F] [([E, E, T, E, E, T, F, E, F, T, E, E, E, E, F], [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F]), ([E, T, E, E, E, E, F, T, F, T, E, E, E, E, F], [E, T, E, E, E, F, E, T, F, T, E, E, E, E, F]), ([E, T, E, E, E, T, F, E, F, E, T, E, E, E, F], [E, T, E, E, F, T, E, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1386 (And.intro z_1557 (And.intro z_1558 trivial)))

theorem z_1560 : le (tf [E, T, E, E, E, T, F, E, T, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, F, E, T, E, F, E, E, E, F] [([E, E, T, E, E, T, F, E, T, E, F, E, E, E, F], [E, E, T, E, F, T, E, E, T, E, F, E, E, E, F]), ([E, T, E, E, E, E, F, T, T, E, F, E, E, E, F], [E, T, E, E, E, F, E, T, T, E, F, E, E, E, F]), ([E, T, E, E, E, T, F, E, E, T, F, E, E, E, F], [E, T, E, E, E, T, F, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1387 (And.intro z_1552 (And.intro z_1559 trivial)))

theorem z_1561 : le (tf [E, T, E, E, E, T, T, F, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, T, F, E, E, F, E, E, E, F] [([E, E, T, E, E, T, T, F, E, E, F, E, E, E, F], [E, E, T, E, E, T, T, F, E, F, E, E, E, E, F]), ([E, T, E, E, E, T, E, F, T, E, F, E, E, E, F], [E, T, E, E, E, T, F, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1542 (And.intro z_1560 trivial))

theorem z_1562 : le (tf [T, F, E, E, E, F, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, E, E, E, F, T, T] [([E, F, T, E, E, F, E, E, E, E, E, E, F, T, T], [F, E, T, E, E, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1077 trivial)

theorem z_1563 : le (tf [T, F, E, E, E, E, F, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, E, E, T, F, E, T] [([E, F, T, E, E, E, F, E, E, E, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T]), ([T, F, E, E, E, E, F, E, E, E, E, E, F, T, T], [T, F, E, E, E, F, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1078 (And.intro z_1562 trivial))

theorem z_1564 : le (tf [T, F, E, E, E, E, E, F, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, E, E, T, F, T, E] [([E, F, T, E, E, E, E, F, E, E, E, T, F, T, E], [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E]), ([T, F, E, E, E, E, E, F, E, E, E, T, F, E, T], [T, F, E, E, E, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1079 (And.intro z_1563 trivial))

theorem z_1565 : le (tf [T, F, E, E, E, E, E, F, E, E, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, E, E, T, T, E, F] [([E, F, T, E, E, E, E, F, E, E, E, T, T, E, F], [F, E, T, E, E, E, E, F, E, E, E, T, T, E, F]), ([T, F, E, E, E, E, E, F, E, E, E, T, E, T, F], [T, F, E, E, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1080 (And.intro z_1564 trivial))

theorem z_1566 : le (tf [T, F, E, E, E, E, E, F, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, E, T, E, E, T, F] [([E, F, T, E, E, E, E, F, E, E, T, E, E, T, F], [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F]), ([T, F, E, E, E, E, E, F, E, E, E, T, E, T, F], [T, F, E, E, E, E, E, F, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1085 (And.intro z_1564 trivial))

theorem z_1567 : le (tf [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F] [([E, F, T, E, E, E, E, E, F, E, T, E, T, E, F], [E, F, T, E, E, E, E, F, E, E, T, E, T, E, F]), ([T, F, E, E, E, E, E, E, F, E, E, T, T, E, F], [T, F, E, E, E, E, E, F, E, E, E, T, T, E, F]), ([T, F, E, E, E, E, E, E, F, E, T, E, E, T, F], [T, F, E, E, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1530 (And.intro z_1565 (And.intro z_1566 trivial)))

theorem z_1568 : le (tf [T, F, E, E, E, E, E, E, E, F, T, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, E, F, T, T, E, E, F] [([E, F, T, E, E, E, E, E, E, F, T, T, E, E, F], [E, F, T, E, E, E, E, E, F, E, T, T, E, E, F]), ([T, F, E, E, E, E, E, E, E, F, T, E, T, E, F], [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1531 (And.intro z_1567 trivial))

theorem z_1569 : le (tf [F, E, T, F, E, E, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, F, E, E, E, E, E, E, E, E, F, T, T] [([F, E, E, F, T, E, E, E, E, E, E, E, F, T, T], [F, E, E, F, T, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_486 trivial)

theorem z_1570 : le (tf [T, F, E, F, E, E, E, E, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, E, F, E, E, E, E, E, E, E, E, F, T, T] [([E, F, T, F, E, E, E, E, E, E, E, E, F, T, T], [F, E, T, F, E, E, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1569 trivial)

theorem z_1571 : le (tf [T, F, E, E, F, E, E, E, E, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, F, E, E, E, E, E, E, T, F, E, T] [([E, F, T, E, F, E, E, E, E, E, E, T, F, E, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T]), ([T, F, E, E, F, E, E, E, E, E, E, E, F, T, T], [T, F, E, F, E, E, E, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_849 (And.intro z_1570 trivial))

theorem z_1572 : le (tf [T, F, E, E, E, F, E, E, E, E, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, E, E, T, F, T, E] [([E, F, T, E, E, F, E, E, E, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E]), ([T, F, E, E, E, F, E, E, E, E, E, T, F, E, T], [T, F, E, E, F, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_850 (And.intro z_1571 trivial))

theorem z_1573 : le (tf [T, F, E, E, E, F, E, E, E, E, T, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, E, T, E, E, T, F] [([E, F, T, E, E, F, E, E, E, E, T, E, E, T, F], [F, E, T, E, E, F, E, E, E, E, T, E, E, T, F]), ([T, F, E, E, E, F, E, E, E, E, E, T, E, T, F], [T, F, E, E, E, F, E, E, E, E, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_851 (And.intro z_1572 trivial))

theorem z_1574 : le (tf [T, F, E, E, E, E, F, E, E, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, T, E, E, E, T, F] [([E, F, T, E, E, E, F, E, E, T, E, E, E, T, F], [F, E, T, E, E, E, F, E, E, T, E, E, E, T, F]), ([T, F, E, E, E, E, F, E, E, E, T, E, E, T, F], [T, F, E, E, E, F, E, E, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_852 (And.intro z_1573 trivial))

theorem z_1575 : le (tf [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F] [([E, F, T, E, E, E, E, F, T, E, E, E, E, T, F], [F, E, T, E, E, E, E, F, T, E, E, E, E, T, F]), ([T, F, E, E, E, E, E, F, E, T, E, E, E, T, F], [T, F, E, E, E, E, F, E, E, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_853 (And.intro z_1574 trivial))

theorem z_1576 : le (tf [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F] [([E, F, T, E, E, E, E, E, T, F, E, E, T, E, F], [E, F, T, E, E, E, E, F, T, E, E, E, T, E, F]), ([T, F, E, E, E, E, E, E, E, F, T, E, T, E, F], [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F]), ([T, F, E, E, E, E, E, E, T, F, E, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_951 (And.intro z_1567 (And.intro z_1575 trivial)))

theorem z_1577 : le (tf [T, E, F, E, E, E, E, E, T, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, E, T, F, E, T, E, E, F] [([E, T, F, E, E, E, E, E, T, F, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F]), ([T, E, F, E, E, E, E, E, E, F, T, T, E, E, F], [T, F, E, E, E, E, E, E, E, F, T, T, E, E, F]), ([T, E, F, E, E, E, E, E, T, F, E, E, T, E, F], [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1068 (And.intro z_1568 (And.intro z_1576 trivial)))

theorem z_1578 : le (tf [T, E, E, F, E, E, E, E, T, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, E, T, F, T, E, E, E, F] [([E, T, E, F, E, E, E, E, T, F, T, E, E, E, F], [E, T, F, E, E, E, E, E, T, F, T, E, E, E, F]), ([T, E, E, F, E, E, E, E, T, F, E, T, E, E, F], [T, E, F, E, E, E, E, E, T, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1069 (And.intro z_1577 trivial))

theorem z_1579 : le (tf [T, E, E, F, E, E, E, E, T, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, E, T, T, E, F, E, E, F] [([E, T, E, F, E, E, E, E, T, T, E, F, E, E, F], [E, T, F, E, E, E, E, E, T, T, E, F, E, E, F]), ([T, E, E, F, E, E, E, E, T, E, T, F, E, E, F], [T, E, E, F, E, E, E, E, T, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1070 (And.intro z_1578 trivial))

theorem z_1580 : le (tf [F, E, T, E, E, E, E, F, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, E, E, F, T, T] [([F, E, E, T, E, E, E, F, E, E, E, E, F, T, T], [F, E, E, T, E, E, F, E, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1026 trivial)

theorem z_1581 : le (tf [F, E, T, E, E, E, E, E, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, E, E, T, F, E, T] [([F, E, E, T, E, E, E, E, F, E, E, T, F, E, T], [F, E, E, T, E, E, E, F, E, E, E, T, F, E, T]), ([F, E, T, E, E, E, E, E, F, E, E, E, F, T, T], [F, E, T, E, E, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1027 (And.intro z_1580 trivial))

theorem z_1582 : le (tf [F, E, T, E, E, E, E, E, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, E, F, E, T, F, T, E] [([F, E, E, T, E, E, E, E, E, F, E, T, F, T, E], [F, E, E, T, E, E, E, E, F, E, E, T, F, T, E]), ([F, E, T, E, E, E, E, E, E, F, E, T, F, E, T], [F, E, T, E, E, E, E, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1028 (And.intro z_1581 trivial))

theorem z_1583 : le (tf [F, E, T, E, E, E, E, E, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, E, F, E, T, T, E, F] [([F, E, E, T, E, E, E, E, E, F, E, T, T, E, F], [F, E, E, T, E, E, E, E, F, E, E, T, T, E, F]), ([F, E, T, E, E, E, E, E, E, F, E, T, E, T, F], [F, E, T, E, E, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1074 (And.intro z_1582 trivial))

theorem z_1584 : le (tf [F, E, T, E, E, E, E, E, F, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, T, E, E, E, T, F] [([F, E, E, T, E, E, E, E, F, T, E, E, E, T, F], [F, E, E, T, E, E, E, F, E, T, E, E, E, T, F]), ([F, E, T, E, E, E, E, E, F, E, T, E, E, T, F], [F, E, T, E, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_535 (And.intro z_1085 trivial))

theorem z_1585 : le (tf [F, E, T, E, E, E, E, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, E, T, F, E, T, E, F] [([F, E, E, T, E, E, E, E, E, T, F, E, T, E, F], [F, E, E, T, E, E, E, E, E, T, F, E, T, F, E]), ([F, E, T, E, E, E, E, E, E, E, F, T, T, E, F], [F, E, T, E, E, E, E, E, E, F, E, T, T, E, F]), ([F, E, T, E, E, E, E, E, E, T, F, E, E, T, F], [F, E, T, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1025 (And.intro z_1583 (And.intro z_1584 trivial)))

theorem z_1586 : le (tf [F, E, T, E, E, E, E, E, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, E, F, E, E, T, F] [([F, E, E, T, E, E, E, E, T, E, F, E, E, T, F], [F, E, E, T, E, E, E, E, T, F, E, E, E, T, F]), ([F, E, T, E, E, E, E, E, E, T, F, E, E, T, F], [F, E, T, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1030 (And.intro z_1584 trivial))

theorem z_1587 : le (tf [F, E, T, E, E, E, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, E, E, F, T, E, F] [([F, E, E, T, E, E, E, E, T, E, E, F, T, E, F], [F, E, E, T, E, E, E, E, T, E, F, E, T, E, F]), ([F, E, T, E, E, E, E, E, E, T, E, F, T, E, F], [F, E, T, E, E, E, E, E, E, T, F, E, T, E, F]), ([F, E, T, E, E, E, E, E, T, E, E, F, E, T, F], [F, E, T, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1031 (And.intro z_1585 (And.intro z_1586 trivial)))

theorem z_1588 : le (tf [T, F, E, E, E, E, E, F, E, E, E, E, F, T, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, E, E, E, F, T, T] [([E, F, T, E, E, E, E, F, E, E, E, E, F, T, T], [F, E, T, E, E, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1580 trivial)

theorem z_1589 : le (tf [T, F, E, E, E, E, E, E, F, E, E, T, F, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, E, E, T, F, E, T] [([E, F, T, E, E, E, E, E, F, E, E, T, F, E, T], [F, E, T, E, E, E, E, E, F, E, E, T, F, E, T]), ([T, F, E, E, E, E, E, E, F, E, E, E, F, T, T], [T, F, E, E, E, E, E, F, E, E, E, E, F, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1581 (And.intro z_1588 trivial))

theorem z_1590 : le (tf [T, F, E, E, E, E, E, E, E, F, E, T, F, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, E, F, E, T, F, T, E] [([E, F, T, E, E, E, E, E, E, F, E, T, F, T, E], [F, E, T, E, E, E, E, E, E, F, E, T, F, T, E]), ([T, F, E, E, E, E, E, E, E, F, E, T, F, E, T], [T, F, E, E, E, E, E, E, F, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1582 (And.intro z_1589 trivial))

theorem z_1591 : le (tf [T, F, E, E, E, E, E, E, E, F, E, T, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, E, F, E, T, T, E, F] [([E, F, T, E, E, E, E, E, E, F, E, T, T, E, F], [F, E, T, E, E, E, E, E, E, F, E, T, T, E, F]), ([T, F, E, E, E, E, E, E, E, F, E, T, E, T, F], [T, F, E, E, E, E, E, E, E, F, E, T, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1583 (And.intro z_1590 trivial))

theorem z_1592 : le (tf [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F] [([E, F, T, E, E, E, E, E, F, T, E, E, E, T, F], [F, E, T, E, E, E, E, E, F, T, E, E, E, T, F]), ([T, F, E, E, E, E, E, E, F, E, T, E, E, T, F], [T, F, E, E, E, E, E, F, E, E, T, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1584 (And.intro z_1566 trivial))

theorem z_1593 : le (tf [T, F, E, E, E, E, E, E, E, T, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, E, T, F, E, T, E, F] [([E, F, T, E, E, E, E, E, E, T, F, E, T, E, F], [F, E, T, E, E, E, E, E, E, T, F, E, T, E, F]), ([T, F, E, E, E, E, E, E, E, E, F, T, T, E, F], [T, F, E, E, E, E, E, E, E, F, E, T, T, E, F]), ([T, F, E, E, E, E, E, E, E, T, F, E, E, T, F], [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1585 (And.intro z_1591 (And.intro z_1592 trivial)))

theorem z_1594 : le (tf [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F] [([E, F, T, E, E, E, E, E, T, E, F, E, E, T, F], [F, E, T, E, E, E, E, E, T, E, F, E, E, T, F]), ([T, F, E, E, E, E, E, E, E, T, F, E, E, T, F], [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1586 (And.intro z_1592 trivial))

theorem z_1595 : le (tf [T, F, E, E, E, E, E, E, T, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, T, E, E, F, T, E, F] [([E, F, T, E, E, E, E, E, T, E, E, F, T, E, F], [F, E, T, E, E, E, E, E, T, E, E, F, T, E, F]), ([T, F, E, E, E, E, E, E, E, T, E, F, T, E, F], [T, F, E, E, E, E, E, E, E, T, F, E, T, E, F]), ([T, F, E, E, E, E, E, E, T, E, E, F, E, T, F], [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1587 (And.intro z_1593 (And.intro z_1594 trivial)))

theorem z_1596 : le (tf [F, E, T, E, E, E, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, E, E, F, E, T, F] [([F, E, E, T, E, E, E, T, E, E, E, F, E, T, F], [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F]), ([F, E, T, E, E, E, E, E, T, E, E, F, E, T, F], [F, E, T, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1032 (And.intro z_1586 trivial))

theorem z_1597 : le (tf [T, F, E, E, E, E, E, T, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, E, E, E, F, E, T, F] [([E, F, T, E, E, E, E, T, E, E, E, F, E, T, F], [F, E, T, E, E, E, E, T, E, E, E, F, E, T, F]), ([T, F, E, E, E, E, E, E, T, E, E, F, E, T, F], [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1596 (And.intro z_1594 trivial))

theorem z_1598 : le (tf [T, E, F, E, E, E, E, T, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, E, E, E, F, T, E, F] [([E, T, F, E, E, E, E, T, E, E, E, F, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F]), ([T, E, F, E, E, E, E, E, T, E, E, F, T, E, F], [T, F, E, E, E, E, E, E, T, E, E, F, T, E, F]), ([T, E, F, E, E, E, E, T, E, E, E, F, E, T, F], [T, F, E, E, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1091 (And.intro z_1595 (And.intro z_1597 trivial)))

theorem z_1599 : le (tf [T, E, E, F, E, E, E, T, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, T, E, E, T, F, E, E, F] [([E, T, E, F, E, E, E, T, E, E, T, F, E, E, F], [E, T, F, E, E, E, E, T, E, E, T, F, E, E, F]), ([T, E, E, F, E, E, E, E, T, E, T, F, E, E, F], [T, E, E, F, E, E, E, E, T, F, T, E, E, E, F]), ([T, E, E, F, E, E, E, T, E, E, E, F, T, E, F], [T, E, F, E, E, E, E, T, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1092 (And.intro z_1578 (And.intro z_1598 trivial)))

theorem z_1600 : le (tf [T, E, E, E, F, E, E, T, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, T, E, T, E, F, E, E, F] [([E, T, E, E, F, E, E, T, E, T, E, F, E, E, F], [E, T, E, F, E, E, E, T, E, T, E, F, E, E, F]), ([T, E, E, E, F, E, E, E, T, T, E, F, E, E, F], [T, E, E, F, E, E, E, E, T, T, E, F, E, E, F]), ([T, E, E, E, F, E, E, T, E, E, T, F, E, E, F], [T, E, E, F, E, E, E, T, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1136 (And.intro z_1579 (And.intro z_1599 trivial)))

theorem z_1601 : le (tf [T, E, E, E, E, F, E, T, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, F, E, T, T, E, E, F, E, E, F] [([E, T, E, E, E, F, E, T, T, E, E, F, E, E, F], [E, T, E, E, E, F, E, T, T, E, F, E, E, E, F]), ([T, E, E, E, E, F, E, T, E, T, E, F, E, E, F], [T, E, E, E, F, E, E, T, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1552 (And.intro z_1600 trivial))

theorem z_1602 : le (tf [T, E, F, E, E, E, E, E, E, T, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, E, E, T, F, T, E, E, F] [([E, T, F, E, E, E, E, E, E, T, F, T, E, E, F], [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F]), ([T, E, F, E, E, E, E, E, E, T, F, E, T, E, F], [T, F, E, E, E, E, E, E, E, T, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1547 (And.intro z_1593 trivial))

theorem z_1603 : le (tf [T, E, F, E, E, E, E, E, T, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, E, T, E, F, E, T, E, F] [([E, T, F, E, E, E, E, E, T, E, F, E, T, E, F], [E, T, F, E, E, E, E, E, T, F, E, E, T, E, F]), ([T, E, F, E, E, E, E, E, E, T, F, E, T, E, F], [T, F, E, E, E, E, E, E, E, T, F, E, T, E, F]), ([T, E, F, E, E, E, E, E, T, E, F, E, E, T, F], [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1089 (And.intro z_1593 (And.intro z_1594 trivial)))

theorem z_1604 : le (tf [T, E, E, F, E, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, E, T, E, F, T, E, E, F] [([E, T, E, F, E, E, E, E, T, E, F, T, E, E, F], [E, T, F, E, E, E, E, E, T, E, F, T, E, E, F]), ([T, E, E, F, E, E, E, E, E, T, F, T, E, E, F], [T, E, F, E, E, E, E, E, E, T, F, T, E, E, F]), ([T, E, E, F, E, E, E, E, T, E, F, E, T, E, F], [T, E, F, E, E, E, E, E, T, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1548 (And.intro z_1602 (And.intro z_1603 trivial)))

theorem z_1605 : le (tf [T, E, E, E, F, E, E, E, T, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, E, T, T, F, E, E, E, F] [([E, T, E, E, F, E, E, E, T, T, F, E, E, E, F], [E, T, E, F, E, E, E, E, T, T, F, E, E, E, F]), ([T, E, E, E, F, E, E, E, T, E, F, T, E, E, F], [T, E, E, F, E, E, E, E, T, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1549 (And.intro z_1604 trivial))

theorem z_1606 : le (tf [T, E, F, E, E, E, E, T, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, E, E, F, E, E, T, F] [([E, T, F, E, E, E, E, T, E, E, F, E, E, T, F], [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F]), ([T, E, F, E, E, E, E, E, T, E, F, E, E, T, F], [T, F, E, E, E, E, E, E, T, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1090 (And.intro z_1594 trivial))

theorem z_1607 : le (tf [T, E, E, F, E, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, T, E, E, F, E, T, E, F] [([E, T, E, F, E, E, E, T, E, E, F, E, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F]), ([T, E, E, F, E, E, E, E, T, E, F, E, T, E, F], [T, E, F, E, E, E, E, E, T, E, F, E, T, E, F]), ([T, E, E, F, E, E, E, T, E, E, F, E, E, T, F], [T, E, F, E, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1091 (And.intro z_1603 (And.intro z_1606 trivial)))

theorem z_1608 : le (tf [T, E, E, E, F, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, T, E, E, F, T, E, E, F] [([E, T, E, E, F, E, E, T, E, E, F, T, E, E, F], [E, T, E, F, E, E, E, T, E, E, F, T, E, E, F]), ([T, E, E, E, F, E, E, E, T, E, F, T, E, E, F], [T, E, E, F, E, E, E, E, T, E, F, T, E, E, F]), ([T, E, E, E, F, E, E, T, E, E, F, E, T, E, F], [T, E, E, F, E, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1550 (And.intro z_1604 (And.intro z_1607 trivial)))

theorem z_1609 : le (tf [T, E, E, E, E, F, E, T, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, F, E, T, E, T, F, E, E, E, F] [([E, T, E, E, E, F, E, T, E, T, F, E, E, E, F], [E, T, E, E, F, E, E, T, E, T, F, E, E, E, F]), ([T, E, E, E, E, F, E, E, T, T, F, E, E, E, F], [T, E, E, E, F, E, E, E, T, T, F, E, E, E, F]), ([T, E, E, E, E, F, E, T, E, E, F, T, E, E, F], [T, E, E, E, F, E, E, T, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1551 (And.intro z_1605 (And.intro z_1608 trivial)))

theorem z_1610 : le (tf [T, F, E, E, E, E, E, T, E, F, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, E, F, E, E, E, T, F] [([E, F, T, E, E, E, E, T, E, F, E, E, E, T, F], [F, E, T, E, E, E, E, T, E, F, E, E, E, T, F]), ([T, F, E, E, E, E, E, E, T, F, E, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_854 (And.intro z_1575 trivial))

theorem z_1611 : le (tf [T, F, E, E, E, E, E, T, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, E, E, F, E, T, E, F] [([E, F, T, E, E, E, E, T, E, E, F, E, T, E, F], [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F]), ([T, F, E, E, E, E, E, E, T, E, F, E, T, E, F], [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F]), ([T, F, E, E, E, E, E, T, E, E, F, E, E, T, F], [T, F, E, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_855 (And.intro z_1576 (And.intro z_1610 trivial)))

theorem z_1612 : le (tf [T, E, F, E, E, E, E, T, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, E, E, F, T, E, E, F] [([E, T, F, E, E, E, E, T, E, E, F, T, E, E, F], [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F]), ([T, E, F, E, E, E, E, E, T, E, F, T, E, E, F], [T, E, F, E, E, E, E, E, T, F, E, T, E, E, F]), ([T, E, F, E, E, E, E, T, E, E, F, E, T, E, F], [T, F, E, E, E, E, E, T, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1123 (And.intro z_1577 (And.intro z_1611 trivial)))

theorem z_1613 : le (tf [T, F, E, E, E, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, E, E, F, E, E, T, F] [([E, F, T, E, E, E, T, E, E, E, F, E, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F]), ([T, F, E, E, E, E, E, T, E, E, F, E, E, T, F], [T, F, E, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_964 (And.intro z_1610 trivial))

theorem z_1614 : le (tf [T, E, F, E, E, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, E, E, E, F, E, T, E, F] [([E, T, F, E, E, E, T, E, E, E, F, E, T, E, F], [E, T, F, E, E, E, T, E, E, F, E, E, T, E, F]), ([T, E, F, E, E, E, E, T, E, E, F, E, T, E, F], [T, F, E, E, E, E, E, T, E, E, F, E, T, E, F]), ([T, E, F, E, E, E, T, E, E, E, F, E, E, T, F], [T, F, E, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1127 (And.intro z_1611 (And.intro z_1613 trivial)))

theorem z_1615 : le (tf [T, E, E, F, E, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, E, E, F, T, E, E, F] [([E, T, E, F, E, E, T, E, E, E, F, T, E, E, F], [E, T, F, E, E, E, T, E, E, E, F, T, E, E, F]), ([T, E, E, F, E, E, E, T, E, E, F, T, E, E, F], [T, E, F, E, E, E, E, T, E, E, F, T, E, E, F]), ([T, E, E, F, E, E, T, E, E, E, F, E, T, E, F], [T, E, F, E, E, E, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1128 (And.intro z_1612 (And.intro z_1614 trivial)))

theorem z_1616 : le (tf [T, E, F, E, E, T, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, E, E, F, E, E, T, F] [([E, T, F, E, E, T, E, E, E, E, F, E, E, T, F], [E, T, F, E, E, T, E, E, E, F, E, E, E, T, F]), ([T, E, F, E, E, E, T, E, E, E, F, E, E, T, F], [T, F, E, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1479 (And.intro z_1613 trivial))

theorem z_1617 : le (tf [T, E, E, F, E, T, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, E, E, F, E, T, E, F] [([E, T, E, F, E, T, E, E, E, E, F, E, T, E, F], [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F]), ([T, E, E, F, E, E, T, E, E, E, F, E, T, E, F], [T, E, F, E, E, E, T, E, E, E, F, E, T, E, F]), ([T, E, E, F, E, T, E, E, E, E, F, E, E, T, F], [T, E, F, E, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1480 (And.intro z_1614 (And.intro z_1616 trivial)))

theorem z_1618 : le (tf [T, E, E, E, F, T, E, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, T, E, E, E, E, F, T, E, E, F] [([E, T, E, E, F, T, E, E, E, E, F, T, E, E, F], [E, T, E, F, E, T, E, E, E, E, F, T, E, E, F]), ([T, E, E, E, F, E, T, E, E, E, F, T, E, E, F], [T, E, E, F, E, E, T, E, E, E, F, T, E, E, F]), ([T, E, E, E, F, T, E, E, E, E, F, E, T, E, F], [T, E, E, F, E, T, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1481 (And.intro z_1615 (And.intro z_1617 trivial)))

theorem z_1619 : le (tf [T, E, E, E, E, T, F, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, F, E, E, T, F, E, E, E, F] [([E, T, E, E, E, T, F, E, E, T, F, E, E, E, F], [E, T, E, E, E, T, F, E, F, T, E, E, E, E, F]), ([T, E, E, E, E, E, F, T, E, T, F, E, E, E, F], [T, E, E, E, E, F, E, T, E, T, F, E, E, E, F]), ([T, E, E, E, E, T, F, E, E, E, F, T, E, E, F], [T, E, E, E, F, T, E, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1559 (And.intro z_1609 (And.intro z_1618 trivial)))

theorem z_1620 : le (tf [T, E, E, E, E, T, F, E, T, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, F, E, T, E, E, F, E, E, F] [([E, T, E, E, E, T, F, E, T, E, E, F, E, E, F], [E, T, E, E, E, T, F, E, T, E, F, E, E, E, F]), ([T, E, E, E, E, E, F, T, T, E, E, F, E, E, F], [T, E, E, E, E, F, E, T, T, E, E, F, E, E, F]), ([T, E, E, E, E, T, F, E, E, T, E, F, E, E, F], [T, E, E, E, E, T, F, E, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1560 (And.intro z_1601 (And.intro z_1619 trivial)))

theorem z_1621 : le (tf [T, E, E, E, E, T, T, F, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, T, F, E, E, E, F, E, E, F] [([E, T, E, E, E, T, T, F, E, E, E, F, E, E, F], [E, T, E, E, E, T, T, F, E, E, F, E, E, E, F]), ([T, E, E, E, E, T, E, F, T, E, E, F, E, E, F], [T, E, E, E, E, T, F, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1561 (And.intro z_1620 trivial))

theorem z_1622 : le (tf [T, E, E, F, E, E, T, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, E, E, T, E, F, E, F] [([E, T, E, F, E, E, T, E, E, E, T, E, F, E, F], [E, T, F, E, E, E, T, E, E, E, T, E, F, E, F]), ([T, E, E, F, E, E, E, T, E, E, T, E, F, E, F], [T, E, E, F, E, E, E, T, E, E, T, F, E, E, F]), ([T, E, E, F, E, E, T, E, E, E, E, T, F, E, F], [T, E, E, F, E, E, T, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1129 (And.intro z_1599 (And.intro z_1615 trivial)))

theorem z_1623 : le (tf [T, E, E, E, F, E, T, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, E, E, T, E, E, F, E, F] [([E, T, E, E, F, E, T, E, E, T, E, E, F, E, F], [E, T, E, F, E, E, T, E, E, T, E, E, F, E, F]), ([T, E, E, E, F, E, E, T, E, T, E, E, F, E, F], [T, E, E, E, F, E, E, T, E, T, E, F, E, E, F]), ([T, E, E, E, F, E, T, E, E, E, T, E, F, E, F], [T, E, E, F, E, E, T, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1134 (And.intro z_1600 (And.intro z_1622 trivial)))

theorem z_1624 : le (tf [T, E, F, E, E, E, T, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, E, E, E, E, F, E, T, F] [([E, T, F, E, E, E, T, E, E, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F]), ([T, E, F, E, E, E, E, T, E, E, E, F, E, T, F], [T, F, E, E, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1138 (And.intro z_1597 trivial))

theorem z_1625 : le (tf [T, E, E, F, E, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, E, E, E, F, T, E, F] [([E, T, E, F, E, E, T, E, E, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, E, E, F, T, E, F]), ([T, E, E, F, E, E, E, T, E, E, E, F, T, E, F], [T, E, F, E, E, E, E, T, E, E, E, F, T, E, F]), ([T, E, E, F, E, E, T, E, E, E, E, F, E, T, F], [T, E, F, E, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1139 (And.intro z_1598 (And.intro z_1624 trivial)))

theorem z_1626 : le (tf [T, E, E, E, F, E, T, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, E, E, E, T, F, E, E, F] [([E, T, E, E, F, E, T, E, E, E, T, F, E, E, F], [E, T, E, F, E, E, T, E, E, E, T, F, E, E, F]), ([T, E, E, E, F, E, E, T, E, E, T, F, E, E, F], [T, E, E, F, E, E, E, T, E, E, T, F, E, E, F]), ([T, E, E, E, F, E, T, E, E, E, E, F, T, E, F], [T, E, E, F, E, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1140 (And.intro z_1599 (And.intro z_1625 trivial)))

theorem z_1627 : le (tf [T, E, F, E, T, E, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, T, E, E, E, E, E, E, F, E, T, F] [([E, T, F, E, T, E, E, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F]), ([T, E, F, E, E, T, E, E, E, E, E, F, E, T, F], [T, E, F, E, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1508 (And.intro z_1616 trivial))

theorem z_1628 : le (tf [T, E, E, F, T, E, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, E, E, E, E, E, E, F, T, E, F] [([E, T, E, F, T, E, E, E, E, E, E, F, T, E, F], [E, T, F, E, T, E, E, E, E, E, E, F, T, E, F]), ([T, E, E, F, E, T, E, E, E, E, E, F, T, E, F], [T, E, E, F, E, T, E, E, E, E, F, E, T, E, F]), ([T, E, E, F, T, E, E, E, E, E, E, F, E, T, F], [T, E, F, E, T, E, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1509 (And.intro z_1617 (And.intro z_1627 trivial)))

theorem z_1629 : le (tf [T, E, E, E, T, F, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, E, E, E, T, F, E, E, F] [([E, T, E, E, T, F, E, E, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, E, E, F, T, E, E, E, F]), ([T, E, E, E, E, F, T, E, E, E, T, F, E, E, F], [T, E, E, E, F, E, T, E, E, E, T, F, E, E, F]), ([T, E, E, E, T, F, E, E, E, E, E, F, T, E, F], [T, E, E, F, T, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1277 (And.intro z_1626 (And.intro z_1628 trivial)))

theorem z_1630 : le (tf [T, E, E, E, T, F, E, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, E, E, T, E, E, F, E, F] [([E, T, E, E, T, F, E, E, E, T, E, E, F, E, F], [E, T, E, E, T, F, E, E, E, T, E, F, E, E, F]), ([T, E, E, E, E, F, T, E, E, T, E, E, F, E, F], [T, E, E, E, F, E, T, E, E, T, E, E, F, E, F]), ([T, E, E, E, T, F, E, E, E, E, T, E, F, E, F], [T, E, E, E, T, F, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1278 (And.intro z_1623 (And.intro z_1629 trivial)))

theorem z_1631 : le (tf [T, E, E, E, T, E, F, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, F, E, T, E, E, E, F, E, F] [([E, T, E, E, T, E, F, E, T, E, E, E, F, E, F], [E, T, E, E, T, F, E, E, T, E, E, E, F, E, F]), ([T, E, E, E, E, T, F, E, T, E, E, E, F, E, F], [T, E, E, E, E, T, F, E, T, E, E, F, E, E, F]), ([T, E, E, E, T, E, F, E, E, T, E, E, F, E, F], [T, E, E, E, T, F, E, E, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1279 (And.intro z_1620 (And.intro z_1630 trivial)))

theorem z_1632 : le (tf [T, E, E, E, T, E, T, F, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, T, F, E, E, E, E, F, E, F] [([E, T, E, E, T, E, T, F, E, E, E, E, F, E, F], [E, T, E, E, T, F, T, E, E, E, E, E, F, E, F]), ([T, E, E, E, E, T, T, F, E, E, E, E, F, E, F], [T, E, E, E, E, T, T, F, E, E, E, F, E, E, F]), ([T, E, E, E, T, E, E, F, T, E, E, E, F, E, F], [T, E, E, E, T, E, F, E, T, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1476 (And.intro z_1621 (And.intro z_1631 trivial)))

theorem z_1633 : le (tf [T, E, E, E, T, T, E, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, T, E, F, E, E, E, E, E, F, F] [([E, T, E, E, T, T, E, F, E, E, E, E, E, F, F], [E, T, E, E, T, T, F, E, E, E, E, E, E, F, F]), ([T, E, E, E, T, E, T, F, E, E, E, E, E, F, F], [T, E, E, E, T, E, T, F, E, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1281 (And.intro z_1632 trivial))

theorem z_1634 : le (tf [F, E, T, E, E, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, T, E, F, T, E, E, F] [([F, E, E, T, E, E, E, E, T, E, F, T, E, E, F], [F, E, E, T, E, E, E, E, T, F, E, T, E, E, F]), ([F, E, T, E, E, E, E, E, E, T, F, T, E, E, F], [F, E, T, E, E, E, E, E, F, T, E, T, E, E, F]), ([F, E, T, E, E, E, E, E, T, E, F, E, T, E, F], [F, E, T, E, E, E, E, E, T, E, F, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_526 (And.intro z_869 (And.intro z_846 trivial)))

theorem z_1635 : le (tf [F, E, T, E, E, E, E, T, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, E, E, T, F, E, F] [([F, E, E, T, E, E, E, T, E, E, E, T, F, E, F], [F, E, E, T, E, E, E, T, E, E, F, T, E, E, F]), ([F, E, T, E, E, E, E, E, T, E, E, T, F, E, F], [F, E, T, E, E, E, E, E, T, E, F, T, E, E, F]), ([F, E, T, E, E, E, E, T, E, E, E, E, F, T, F], [F, E, T, E, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1095 (And.intro z_1634 (And.intro z_1596 trivial)))

theorem z_1636 : le (tf [F, E, T, E, E, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, E, E, E, F, T, E, F] [([F, E, E, T, E, E, T, E, E, E, E, F, T, E, F], [F, E, E, T, E, E, T, E, E, E, F, E, T, E, F]), ([F, E, T, E, E, E, E, T, E, E, E, F, T, E, F], [F, E, T, E, E, E, E, T, E, E, F, E, T, E, F]), ([F, E, T, E, E, E, T, E, E, E, E, F, E, T, F], [F, E, T, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_963 (And.intro z_855 (And.intro z_964 trivial)))

theorem z_1637 : le (tf [F, E, T, E, E, E, T, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, T, E, E, E, E, T, E, F, F] [([F, E, E, T, E, E, T, E, E, E, E, T, E, F, F], [F, E, E, T, E, E, T, E, E, E, E, T, F, E, F]), ([F, E, T, E, E, E, E, T, E, E, E, T, E, F, F], [F, E, T, E, E, E, E, T, E, E, E, T, F, E, F]), ([F, E, T, E, E, E, T, E, E, E, E, E, T, F, F], [F, E, T, E, E, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1097 (And.intro z_1635 (And.intro z_1636 trivial)))

theorem z_1638 : le (tf [T, F, E, E, F, E, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [T, F, E, E, F, E, E, E, E, E, E, F, E, T, T] [([E, F, T, E, F, E, E, E, E, E, E, F, E, T, T], [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_829 trivial)

theorem z_1639 : le (tf [T, F, E, E, E, F, E, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, F, E, E, E, E, E, F, T, E, T] [([E, F, T, E, E, F, E, E, E, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T]), ([T, F, E, E, E, F, E, E, E, E, E, F, E, T, T], [T, F, E, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_830 (And.intro z_1638 trivial))

theorem z_1640 : le (tf [T, F, E, E, E, E, F, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, E, E, F, T, T, E] [([E, F, T, E, E, E, F, E, E, E, E, F, T, T, E], [F, E, T, E, E, E, F, E, E, E, E, F, T, T, E]), ([T, F, E, E, E, E, F, E, E, E, E, F, T, E, T], [T, F, E, E, E, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_831 (And.intro z_1639 trivial))

theorem z_1641 : le (tf [T, F, E, E, E, E, F, E, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, E, T, F, E, E, T] [([E, F, T, E, E, E, F, E, E, E, T, F, E, E, T], [F, E, T, E, E, E, F, E, E, E, T, F, E, E, T]), ([T, F, E, E, E, E, F, E, E, E, E, F, T, E, T], [T, F, E, E, E, F, E, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_832 (And.intro z_1639 trivial))

theorem z_1642 : le (tf [T, F, E, E, E, E, E, F, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, E, T, F, E, T, E] [([E, F, T, E, E, E, E, F, E, E, T, F, E, T, E], [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E]), ([T, F, E, E, E, E, E, F, E, E, E, F, T, T, E], [T, F, E, E, E, E, F, E, E, E, E, F, T, T, E]), ([T, F, E, E, E, E, E, F, E, E, T, F, E, E, T], [T, F, E, E, E, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_833 (And.intro z_1640 (And.intro z_1641 trivial)))

theorem z_1643 : le (tf [T, F, E, E, E, E, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, E, T, F, T, E, E] [([E, F, T, E, E, E, E, E, F, E, T, F, T, E, E], [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E]), ([T, F, E, E, E, E, E, E, F, E, T, F, E, T, E], [T, F, E, E, E, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_834 (And.intro z_1642 trivial))

theorem z_1644 : le (tf [T, F, E, E, E, E, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, E, T, T, E, F, E] [([E, F, T, E, E, E, E, E, F, E, T, T, E, F, E], [F, E, T, E, E, E, E, E, F, E, T, T, E, F, E]), ([T, F, E, E, E, E, E, E, F, E, T, E, T, F, E], [T, F, E, E, E, E, E, E, F, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_868 (And.intro z_1643 trivial))

theorem z_1645 : le (tf [T, F, E, E, E, E, F, E, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, F, E, E, E, T, E, E, F, T] [([E, F, T, E, E, E, F, E, E, E, T, E, E, F, T], [F, E, T, E, E, E, F, E, E, E, T, E, E, F, T]), ([T, F, E, E, E, E, F, E, E, E, E, T, E, F, T], [T, F, E, E, E, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_836 (And.intro z_1563 trivial))

theorem z_1646 : le (tf [T, F, E, E, E, E, E, F, E, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, F, E, T, E, E, E, F, T] [([E, F, T, E, E, E, E, F, E, T, E, E, E, F, T], [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T]), ([T, F, E, E, E, E, E, F, E, E, T, E, E, F, T], [T, F, E, E, E, E, F, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_837 (And.intro z_1645 trivial))

theorem z_1647 : le (tf [T, F, E, E, E, E, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, T, E, E, T, F, E] [([E, F, T, E, E, E, E, E, F, T, E, E, T, F, E], [F, E, T, E, E, E, E, E, F, T, E, E, T, F, E]), ([T, F, E, E, E, E, E, E, F, E, T, E, T, F, E], [T, F, E, E, E, E, E, E, F, E, T, F, T, E, E]), ([T, F, E, E, E, E, E, E, F, T, E, E, E, F, T], [T, F, E, E, E, E, E, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_838 (And.intro z_1643 (And.intro z_1646 trivial)))

theorem z_1648 : le (tf [T, F, E, E, E, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, F, T, E, T, E, E, F] [([E, F, T, E, E, E, E, E, F, T, E, T, E, E, F], [F, E, T, E, E, E, E, E, F, T, E, T, E, E, F]), ([T, F, E, E, E, E, E, E, F, E, T, T, E, E, F], [T, F, E, E, E, E, E, E, F, E, T, T, E, F, E]), ([T, F, E, E, E, E, E, E, F, T, E, E, T, E, F], [T, F, E, E, E, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_869 (And.intro z_1644 (And.intro z_1647 trivial)))

theorem z_1649 : le (tf [T, F, E, E, E, E, E, E, T, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, E, T, E, F, T, E, E, F] [([E, F, T, E, E, E, E, E, T, E, F, T, E, E, F], [F, E, T, E, E, E, E, E, T, E, F, T, E, E, F]), ([T, F, E, E, E, E, E, E, E, T, F, T, E, E, F], [T, F, E, E, E, E, E, E, F, T, E, T, E, E, F]), ([T, F, E, E, E, E, E, E, T, E, F, E, T, E, F], [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1634 (And.intro z_1648 (And.intro z_1576 trivial)))

theorem z_1650 : le (tf [T, F, E, E, E, E, E, T, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, E, T, E, E, E, T, F, E, F] [([E, F, T, E, E, E, E, T, E, E, E, T, F, E, F], [F, E, T, E, E, E, E, T, E, E, E, T, F, E, F]), ([T, F, E, E, E, E, E, E, T, E, E, T, F, E, F], [T, F, E, E, E, E, E, E, T, E, F, T, E, E, F]), ([T, F, E, E, E, E, E, T, E, E, E, E, F, T, F], [T, F, E, E, E, E, E, T, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1635 (And.intro z_1649 (And.intro z_1597 trivial)))

theorem z_1651 : le (tf [T, F, E, E, E, E, T, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, E, E, E, F, T, E, F] [([E, F, T, E, E, E, T, E, E, E, E, F, T, E, F], [F, E, T, E, E, E, T, E, E, E, E, F, T, E, F]), ([T, F, E, E, E, E, E, T, E, E, E, F, T, E, F], [T, F, E, E, E, E, E, T, E, E, F, E, T, E, F]), ([T, F, E, E, E, E, T, E, E, E, E, F, E, T, F], [T, F, E, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1636 (And.intro z_1611 (And.intro z_1613 trivial)))

theorem z_1652 : le (tf [T, F, E, E, E, E, T, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, E, T, E, E, E, E, T, E, F, F] [([E, F, T, E, E, E, T, E, E, E, E, T, E, F, F], [F, E, T, E, E, E, T, E, E, E, E, T, E, F, F]), ([T, F, E, E, E, E, E, T, E, E, E, T, E, F, F], [T, F, E, E, E, E, E, T, E, E, E, T, F, E, F]), ([T, F, E, E, E, E, T, E, E, E, E, E, T, F, F], [T, F, E, E, E, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1637 (And.intro z_1650 (And.intro z_1651 trivial)))

theorem z_1653 : le (tf [T, F, E, E, E, T, E, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, F, E, E, E, T, E, E, E, E, E, E, T, F, F] [([E, F, T, E, E, T, E, E, E, E, E, E, T, F, F], [E, F, T, E, E, T, E, E, E, E, E, F, T, E, F]), ([T, F, E, E, E, E, T, E, E, E, E, E, T, F, F], [T, F, E, E, E, E, T, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_999 (And.intro z_1651 trivial))

theorem z_1654 : le (tf [T, E, F, E, E, T, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, E, E, E, T, E, F, F] [([E, T, F, E, E, T, E, E, E, E, E, T, E, F, F], [E, T, F, E, E, T, E, E, E, E, E, T, F, E, F]), ([T, E, F, E, E, E, T, E, E, E, E, T, E, F, F], [T, F, E, E, E, E, T, E, E, E, E, T, E, F, F]), ([T, E, F, E, E, T, E, E, E, E, E, E, T, F, F], [T, F, E, E, E, T, E, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1496 (And.intro z_1652 (And.intro z_1653 trivial)))

theorem z_1655 : le (tf [T, E, E, F, E, T, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, E, E, T, E, E, F, F] [([E, T, E, F, E, T, E, E, E, E, T, E, E, F, F], [E, T, F, E, E, T, E, E, E, E, T, E, E, F, F]), ([T, E, E, F, E, E, T, E, E, E, T, E, E, F, F], [T, E, E, F, E, E, T, E, E, E, T, E, F, E, F]), ([T, E, E, F, E, T, E, E, E, E, E, T, E, F, F], [T, E, F, E, E, T, E, E, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1497 (And.intro z_1622 (And.intro z_1654 trivial)))

theorem z_1656 : le (tf [E, T, F, T, E, E, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, E, E, E, E, F, E, T, F] [([E, T, F, E, T, E, E, E, E, E, E, F, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1508 trivial)

theorem z_1657 : le (tf [T, E, F, T, E, E, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, F, T, E, E, E, E, E, E, E, E, F, T, F] [([E, T, F, T, E, E, E, E, E, E, E, E, F, T, F], [E, T, F, T, E, E, E, E, E, E, E, F, E, T, F]), ([T, E, F, E, T, E, E, E, E, E, E, E, F, T, F], [T, E, F, E, T, E, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1656 (And.intro z_1627 trivial))

theorem z_1658 : le (tf [T, E, E, T, F, E, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, E, E, E, T, F, E, F] [([E, T, E, T, F, E, E, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F]), ([T, E, E, E, F, T, E, E, E, E, E, T, F, E, F], [T, E, E, E, F, T, E, E, E, E, F, T, E, E, F]), ([T, E, E, T, F, E, E, E, E, E, E, E, F, T, F], [T, E, F, T, E, E, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1484 (And.intro z_1618 (And.intro z_1657 trivial)))

theorem z_1659 : le (tf [T, E, E, T, F, E, E, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, E, E, T, E, E, F, F] [([E, T, E, T, F, E, E, E, E, E, T, E, E, F, F], [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F]), ([T, E, E, E, F, T, E, E, E, E, T, E, E, F, F], [T, E, E, F, E, T, E, E, E, E, T, E, E, F, F]), ([T, E, E, T, F, E, E, E, E, E, E, T, E, F, F], [T, E, E, T, F, E, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1500 (And.intro z_1655 (And.intro z_1658 trivial)))

theorem z_1660 : le (tf [T, E, E, T, E, F, E, E, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, F, E, E, E, T, E, E, E, F, F] [([E, T, E, T, E, F, E, E, E, T, E, E, E, F, F], [E, T, E, T, F, E, E, E, E, T, E, E, E, F, F]), ([T, E, E, E, T, F, E, E, E, T, E, E, E, F, F], [T, E, E, E, T, F, E, E, E, T, E, E, F, E, F]), ([T, E, E, T, E, F, E, E, E, E, T, E, E, F, F], [T, E, E, T, F, E, E, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1501 (And.intro z_1630 (And.intro z_1659 trivial)))

theorem z_1661 : le (tf [T, E, E, T, E, E, F, E, T, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, F, E, T, E, E, E, E, F, F] [([E, T, E, T, E, E, F, E, T, E, E, E, E, F, F], [E, T, E, T, E, F, E, E, T, E, E, E, E, F, F]), ([T, E, E, E, T, E, F, E, T, E, E, E, E, F, F], [T, E, E, E, T, E, F, E, T, E, E, E, F, E, F]), ([T, E, E, T, E, E, F, E, E, T, E, E, E, F, F], [T, E, E, T, E, F, E, E, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1502 (And.intro z_1631 (And.intro z_1660 trivial)))

theorem z_1662 : le (tf [T, E, E, T, E, E, T, F, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, T, F, E, E, E, E, E, F, F] [([E, T, E, T, E, E, T, F, E, E, E, E, E, F, F], [E, T, E, T, E, F, T, E, E, E, E, E, E, F, F]), ([T, E, E, E, T, E, T, F, E, E, E, E, E, F, F], [T, E, E, E, T, E, T, F, E, E, E, E, F, E, F]), ([T, E, E, T, E, E, E, F, T, E, E, E, E, F, F], [T, E, E, T, E, E, F, E, T, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1488 (And.intro z_1632 (And.intro z_1661 trivial)))

theorem z_1663 : le (tf [T, E, E, T, E, T, E, E, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, T, E, E, F, E, E, E, E, F, F] [([E, T, E, T, E, T, E, E, F, E, E, E, E, F, F], [E, T, E, T, E, T, E, F, E, E, E, E, E, F, F]), ([T, E, E, E, T, T, E, E, F, E, E, E, E, F, F], [T, E, E, E, T, T, E, F, E, E, E, E, E, F, F]), ([T, E, E, T, E, E, T, E, F, E, E, E, E, F, F], [T, E, E, T, E, E, T, F, E, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1489 (And.intro z_1633 (And.intro z_1662 trivial)))

theorem z_1664 : le (tf [T, E, E, T, T, E, E, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, E, T, T, E, E, E, E, F, E, E, E, F, F] [([E, T, E, T, T, E, E, E, E, F, E, E, E, F, F], [E, T, E, T, T, E, E, E, F, E, E, E, E, F, F]), ([T, E, E, T, E, T, E, E, E, F, E, E, E, F, F], [T, E, E, T, E, T, E, E, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1490 (And.intro z_1663 trivial))

theorem z_1665 : le (tf [E, E, T, T, F, F, E, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, F, E, E, E, E, E, E, E, T, F] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1666 : le (tf [E, E, T, T, F, E, F, E, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, F, E, E, E, E, E, T, E, F] [([E, E, T, E, F, T, F, E, E, E, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F]), ([E, E, T, T, F, E, F, E, E, E, E, E, E, T, F], [E, E, T, T, F, F, E, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1239 (And.intro z_1665 trivial))

theorem z_1667 : le (tf [E, E, T, T, F, E, E, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, F, E, E, E, T, E, E, F] [([E, E, T, E, F, T, E, F, E, E, E, T, E, E, F], [E, E, T, F, E, T, E, F, E, E, E, T, E, E, F]), ([E, E, T, T, F, E, E, F, E, E, E, E, T, E, F], [E, E, T, T, F, E, F, E, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1240 (And.intro z_1666 trivial))

theorem z_1668 : le (tf [E, E, T, T, F, E, E, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, F, E, E, E, F, E, T, E, E, E, F] [([E, E, T, E, F, T, E, E, F, E, T, E, E, E, F], [E, E, T, F, E, T, E, E, F, E, T, E, E, E, F]), ([E, E, T, T, F, E, E, E, F, E, E, T, E, E, F], [E, E, T, T, F, E, E, F, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1241 (And.intro z_1667 trivial))

theorem z_1669 : le (tf [E, T, E, F, E, T, E, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, F, E, E, E, E, T, E, F] [([E, E, T, F, E, T, E, F, E, E, E, E, T, E, F], [E, E, T, F, E, T, F, E, E, E, E, E, T, E, F]), ([E, T, E, F, E, E, T, F, E, E, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F]), ([E, T, E, F, E, T, E, F, E, E, E, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1239 (And.intro z_1265 (And.intro z_1269 trivial)))

theorem z_1670 : le (tf [E, E, F, T, T, F, E, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, E, F, T, T, F, E, E, E, E, E, E, E, T, F] [([E, E, F, T, E, F, T, E, E, E, E, E, E, T, F], [E, E, F, T, F, E, T, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1250 trivial)

theorem z_1671 : le (tf [E, E, F, T, E, T, F, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, T, F, E, E, E, E, F, E, T, E] [([E, E, F, E, T, T, F, E, E, E, E, F, E, T, E], [E, E, F, E, T, T, F, E, E, E, F, E, E, T, E]), ([E, E, F, T, E, E, F, T, E, E, E, F, E, T, E], [E, E, F, T, E, E, F, T, E, E, F, E, E, T, E]), ([E, E, F, T, E, T, F, E, E, E, E, F, E, E, T], [E, F, E, T, E, T, F, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1423 (And.intro z_725 (And.intro z_1236 trivial)))

theorem z_1672 : le (tf [E, E, F, T, F, E, E, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, F, E, E, T, E, E, E, E, F, T, E] [([E, E, F, E, F, T, E, T, E, E, E, E, F, T, E], [E, F, E, E, F, T, E, T, E, E, E, E, F, T, E]), ([E, E, F, T, F, E, E, E, T, E, E, E, F, T, E], [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E]), ([E, E, F, T, F, E, E, T, E, E, E, E, F, E, T], [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_930 (And.intro z_919 (And.intro z_1232 trivial)))

theorem z_1673 : le (tf [E, T, F, F, E, E, E, E, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, F, F, E, E, E, E, T, E, E, E, F, E, T] [([E, T, F, F, E, E, E, E, E, T, E, E, F, E, T], [E, T, F, F, E, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1260 trivial)

theorem z_1674 : le (tf [E, T, F, E, F, E, E, E, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, T, E, E, E, F, T, E] [([E, E, F, T, F, E, E, E, T, E, E, E, F, T, E], [E, F, E, T, F, E, E, E, T, E, E, E, F, T, E]), ([E, T, F, E, F, E, E, E, E, T, E, E, F, T, E], [E, T, F, F, E, E, E, E, E, T, E, E, F, T, E]), ([E, T, F, E, F, E, E, E, T, E, E, E, F, E, T], [E, T, F, F, E, E, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_919 (And.intro z_1261 (And.intro z_1673 trivial)))

theorem z_1675 : le (tf [E, T, F, E, F, E, E, T, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, T, E, E, E, E, F, E, T] [([E, E, F, T, F, E, E, T, E, E, E, E, F, E, T], [E, F, E, T, F, E, E, T, E, E, E, E, F, E, T]), ([E, T, F, E, F, E, E, E, T, E, E, E, F, E, T], [E, T, F, F, E, E, E, E, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1232 (And.intro z_1673 trivial))

theorem z_1676 : le (tf [E, T, F, E, E, F, E, T, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, T, E, E, E, E, F, T, E] [([E, E, F, T, E, F, E, T, E, E, E, E, F, T, E], [E, E, F, T, F, E, E, T, E, E, E, E, F, T, E]), ([E, T, F, E, E, F, E, E, T, E, E, E, F, T, E], [E, T, F, E, F, E, E, E, T, E, E, E, F, T, E]), ([E, T, F, E, E, F, E, T, E, E, E, E, F, E, T], [E, T, F, E, F, E, E, T, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1672 (And.intro z_1674 (And.intro z_1675 trivial)))

theorem z_1677 : le (tf [E, F, E, T, E, F, E, T, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, F, E, T, E, E, E, F, E, E, T] [([E, F, E, E, T, F, E, T, E, E, E, F, E, E, T], [E, F, E, E, T, F, E, T, E, E, F, E, E, E, T]), ([E, F, E, T, E, F, E, E, T, E, E, F, E, E, T], [E, F, E, T, F, E, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_722 (And.intro z_1199 trivial))

theorem z_1678 : le (tf [E, T, F, E, F, E, E, E, T, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, F, E, E, E, T, E, E, F, E, E, T] [([E, E, F, T, F, E, E, E, T, E, E, F, E, E, T], [E, F, E, T, F, E, E, E, T, E, E, F, E, E, T]), ([E, T, F, E, F, E, E, E, E, T, E, F, E, E, T], [E, T, F, F, E, E, E, E, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1199 (And.intro z_1260 trivial))

theorem z_1679 : le (tf [E, T, F, E, E, F, E, T, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, F, E, T, E, E, E, F, E, E, T] [([E, E, F, T, E, F, E, T, E, E, E, F, E, E, T], [E, F, E, T, E, F, E, T, E, E, E, F, E, E, T]), ([E, T, F, E, E, F, E, E, T, E, E, F, E, E, T], [E, T, F, E, F, E, E, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1677 (And.intro z_1678 trivial))

theorem z_1680 : le (tf [E, T, F, E, E, T, F, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, E, E, E, F, E, E, T] [([E, E, F, T, E, T, F, E, E, E, E, F, E, E, T], [E, F, E, T, E, T, F, E, E, E, E, F, E, E, T]), ([E, T, F, E, E, E, F, T, E, E, E, F, E, E, T], [E, T, F, E, E, F, E, T, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1236 (And.intro z_1679 trivial))

theorem z_1681 : le (tf [E, T, F, E, E, T, F, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, F, E, E, E, E, E, F, T, E] [([E, E, F, T, E, T, F, E, E, E, E, E, F, T, E], [E, E, F, T, E, T, F, E, E, E, E, F, E, T, E]), ([E, T, F, E, E, E, F, T, E, E, E, E, F, T, E], [E, T, F, E, E, F, E, T, E, E, E, E, F, T, E]), ([E, T, F, E, E, T, F, E, E, E, E, E, F, E, T], [E, T, F, E, E, T, F, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1671 (And.intro z_1676 (And.intro z_1680 trivial)))

theorem z_1682 : le (tf [E, T, F, E, T, E, F, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, F, E, E, E, E, E, E, T, F] [([E, E, F, T, T, E, F, E, E, E, E, E, E, T, F], [E, E, F, T, T, F, E, E, E, E, E, E, E, T, F]), ([E, T, F, E, E, T, F, E, E, E, E, E, E, T, F], [E, T, F, E, E, T, F, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1670 (And.intro z_1681 trivial))

theorem z_1683 : le (tf [E, T, F, T, E, E, E, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, T, E, E, E, F, E, E, E, E, E, T, F] [([E, T, F, E, T, E, E, F, E, E, E, E, E, T, F], [E, T, F, E, T, E, F, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1682 trivial)

theorem z_1684 : le (tf [E, T, E, T, F, E, E, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, F, E, E, E, E, T, E, F] [([E, E, T, T, F, E, E, F, E, E, E, E, T, E, F], [E, E, T, T, F, E, F, E, E, E, E, E, T, E, F]), ([E, T, E, E, F, T, E, F, E, E, E, E, T, E, F], [E, T, E, F, E, T, E, F, E, E, E, E, T, E, F]), ([E, T, E, T, F, E, E, F, E, E, E, E, E, T, F], [E, T, F, T, E, E, E, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1666 (And.intro z_1669 (And.intro z_1683 trivial)))

theorem z_1685 : le (tf [E, T, E, T, F, E, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, F, E, E, T, E, E, F] [([E, E, T, T, F, E, E, E, F, E, E, T, E, E, F], [E, E, T, T, F, E, E, F, E, E, E, T, E, E, F]), ([E, T, E, E, F, T, E, E, F, E, E, T, E, E, F], [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F]), ([E, T, E, T, F, E, E, E, F, E, E, E, T, E, F], [E, T, E, T, F, E, E, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1667 (And.intro z_1271 (And.intro z_1684 trivial)))

theorem z_1686 : le (tf [E, T, E, T, F, E, E, E, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, F, T, E, E, E, F] [([E, E, T, T, F, E, E, E, E, F, T, E, E, E, F], [E, E, T, T, F, E, E, E, F, E, T, E, E, E, F]), ([E, T, E, E, F, T, E, E, E, F, T, E, E, E, F], [E, T, E, E, F, T, E, E, F, E, T, E, E, E, F]), ([E, T, E, T, F, E, E, E, E, F, E, T, E, E, F], [E, T, E, T, F, E, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1668 (And.intro z_1558 (And.intro z_1685 trivial)))

theorem z_1687 : le (tf [E, T, T, E, F, E, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, E, E, T, F, E, E, F] [([E, T, E, T, F, E, E, E, E, E, T, F, E, E, F], [E, T, E, T, F, E, E, E, E, F, T, E, E, E, F]), ([E, T, T, E, F, E, E, E, E, E, E, F, T, E, F], [E, T, T, F, E, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1686 (And.intro z_1512 trivial))

theorem z_1688 : le (tf [E, T, T, E, E, F, E, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, E, E, T, E, F, E, E, F] [([E, T, E, T, E, F, E, E, E, T, E, F, E, E, F], [E, T, E, T, E, F, E, E, E, T, F, E, E, E, F]), ([E, T, T, E, E, F, E, E, E, E, T, F, E, E, F], [E, T, T, E, F, E, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1485 (And.intro z_1687 trivial))

theorem z_1689 : le (tf [E, T, T, E, E, F, E, E, T, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, E, T, E, E, E, F, E, F] [([E, T, E, T, E, F, E, E, T, E, E, E, F, E, F], [E, T, E, T, E, F, E, E, T, E, E, F, E, E, F]), ([E, T, T, E, E, F, E, E, E, T, E, E, F, E, F], [E, T, T, E, E, F, E, E, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1486 (And.intro z_1688 trivial))

theorem z_1690 : le (tf [E, T, T, E, E, E, F, T, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, E, F, T, E, E, E, E, F, E, F] [([E, T, E, T, E, E, F, T, E, E, E, E, F, E, F], [E, T, E, T, E, F, E, T, E, E, E, E, F, E, F]), ([E, T, T, E, E, E, F, E, T, E, E, E, F, E, F], [E, T, T, E, E, F, E, E, T, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1487 (And.intro z_1689 trivial))

theorem z_1691 : le (tf [E, E, T, T, E, F, E, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, E, F, E, T, E, E, E, F, E, E, F] [([E, E, T, E, T, F, E, T, E, E, E, F, E, E, F], [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F]), ([E, E, T, T, E, F, E, E, T, E, E, F, E, E, F], [E, E, T, T, F, E, E, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1408 (And.intro z_1396 trivial))

theorem z_1692 : le (tf [E, T, E, T, E, E, F, T, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, E, F, T, E, E, E, F, E, E, F] [([E, E, T, T, E, E, F, T, E, E, E, F, E, E, F], [E, E, T, T, E, F, E, T, E, E, E, F, E, E, F]), ([E, T, E, E, T, E, F, T, E, E, E, F, E, E, F], [E, T, E, E, T, F, E, T, E, E, E, F, E, E, F]), ([E, T, E, T, E, E, F, E, T, E, E, F, E, E, F], [E, T, E, T, E, F, E, E, T, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1691 (And.intro z_1475 (And.intro z_1486 trivial)))

theorem z_1693 : le (tf [E, E, E, F, E, T, T, T, F, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, T, F, E, E, E, E, F, E] [([E, E, E, F, E, T, T, E, F, T, E, E, E, F, E], [E, E, E, F, E, T, T, F, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1295 trivial)

theorem z_1694 : le (tf [E, E, E, T, F, E, T, T, F, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, T, F, E, E, E, E, F, E] [([E, E, E, E, F, T, T, T, F, E, E, E, E, F, E], [E, E, E, F, E, T, T, T, F, E, E, E, E, F, E]), ([E, E, E, T, F, E, T, E, F, T, E, E, E, F, E], [E, E, E, T, F, E, T, F, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1693 (And.intro z_1364 trivial))

theorem z_1695 : le (tf [E, E, E, T, F, T, E, T, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, T, F, E, E, E, E, E, F] [([E, E, E, T, F, E, T, T, F, E, E, E, E, E, F], [E, E, E, T, F, E, T, T, F, E, E, E, E, F, E]), ([E, E, E, T, F, T, E, E, F, T, E, E, E, E, F], [E, E, E, T, F, T, E, F, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1694 (And.intro z_1382 trivial))

theorem z_1696 : le (tf [E, E, T, E, E, T, F, T, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, F, T, F, E, E, E, E, E, F] [([E, E, E, T, E, T, F, T, F, E, E, E, E, E, F], [E, E, E, T, F, T, E, T, F, E, E, E, E, E, F]), ([E, E, T, E, E, T, F, E, F, T, E, E, E, E, F], [E, E, T, E, F, T, E, E, F, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1695 (And.intro z_1386 trivial))

theorem z_1697 : le (tf [E, E, E, E, F, E, T, T, T, F, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, T, T, F, F, E, E, E, E] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1698 : le (tf [E, E, E, E, T, F, E, T, T, F, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, T, T, F, F, E, E, E, E] [([E, E, E, E, E, F, T, T, T, F, F, E, E, E, E], [E, E, E, E, F, E, T, T, T, F, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1697 trivial)

theorem z_1699 : le (tf [E, E, E, E, T, T, F, E, T, F, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, F, E, T, F, F, E, E, E, E] [([E, E, E, E, T, E, F, T, T, F, F, E, E, E, E], [E, E, E, E, T, F, E, T, T, F, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1698 trivial)

theorem z_1700 : le (tf [F, E, E, E, E, E, T, F, T, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, T, E, E, F, E, T, E] [([F, E, E, E, E, E, T, F, E, T, E, F, E, T, E], [F, E, E, E, E, F, T, E, E, T, E, F, E, T, E]), ([F, E, E, E, E, E, T, F, T, E, E, F, E, E, T], [F, E, E, E, E, F, T, E, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_1195 trivial))

theorem z_1701 : le (tf [F, E, E, E, E, E, T, T, E, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, T, E, F, E, F, E, T, E] [([F, E, E, E, E, E, T, E, T, F, E, F, E, T, E], [F, E, E, E, E, E, T, F, T, E, E, F, E, T, E]), ([F, E, E, E, E, E, T, T, E, F, E, F, E, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1700 (And.intro z_194 trivial))

theorem z_1702 : le (tf [E, F, E, E, E, E, T, T, E, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, E, F, E, F, T, E, E] [([E, F, E, E, E, E, T, E, T, F, E, F, T, E, E], [E, F, E, E, E, E, T, F, T, E, E, F, T, E, E]), ([E, F, E, E, E, E, T, T, E, F, E, F, E, T, E], [F, E, E, E, E, E, T, T, E, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1305 (And.intro z_1701 trivial))

theorem z_1703 : le (tf [E, E, F, E, E, E, T, T, E, F, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, E, F, T, F, E, E, E] [([E, E, F, E, E, E, T, E, T, F, T, F, E, E, E], [E, E, F, E, E, E, T, F, T, E, T, F, E, E, E]), ([E, E, F, E, E, E, T, T, E, F, E, F, T, E, E], [E, F, E, E, E, E, T, T, E, F, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1306 (And.intro z_1702 trivial))

theorem z_1704 : le (tf [F, E, E, E, E, T, E, T, E, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, F, E, F, E, E, T] [([F, E, E, E, E, E, T, T, E, F, E, F, E, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T]), ([F, E, E, E, E, T, E, E, T, F, E, F, E, E, T], [F, E, E, E, E, T, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 (And.intro z_1310 trivial))

theorem z_1705 : le (tf [E, F, E, E, E, T, E, T, E, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, E, F, E, F, E, T, E] [([E, F, E, E, E, E, T, T, E, F, E, F, E, T, E], [F, E, E, E, E, E, T, T, E, F, E, F, E, T, E]), ([E, F, E, E, E, T, E, E, T, F, E, F, E, T, E], [E, F, E, E, E, T, E, F, T, E, E, F, E, T, E]), ([E, F, E, E, E, T, E, T, E, F, E, F, E, E, T], [F, E, E, E, E, T, E, T, E, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1701 (And.intro z_1311 (And.intro z_1704 trivial)))

theorem z_1706 : le (tf [E, E, F, E, E, T, E, T, E, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, E, F, E, F, T, E, E] [([E, E, F, E, E, E, T, T, E, F, E, F, T, E, E], [E, F, E, E, E, E, T, T, E, F, E, F, T, E, E]), ([E, E, F, E, E, T, E, E, T, F, E, F, T, E, E], [E, E, F, E, E, T, E, F, T, E, E, F, T, E, E]), ([E, E, F, E, E, T, E, T, E, F, E, F, E, T, E], [E, F, E, E, E, T, E, T, E, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1702 (And.intro z_1312 (And.intro z_1705 trivial)))

theorem z_1707 : le (tf [E, E, E, F, E, T, E, T, E, F, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, E, F, T, F, E, E, E] [([E, E, E, F, E, E, T, T, E, F, T, F, E, E, E], [E, E, F, E, E, E, T, T, E, F, T, F, E, E, E]), ([E, E, E, F, E, T, E, E, T, F, T, F, E, E, E], [E, E, E, F, E, T, E, F, T, E, T, F, E, E, E]), ([E, E, E, F, E, T, E, T, E, F, E, F, T, E, E], [E, E, F, E, E, T, E, T, E, F, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1703 (And.intro z_1313 (And.intro z_1706 trivial)))

theorem z_1708 : le (tf [F, E, E, E, E, T, E, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, F, E, E, F, E, T, E] [([F, E, E, E, E, E, T, T, F, E, E, F, E, T, E], [F, E, E, E, E, E, T, T, F, E, F, E, E, T, E]), ([F, E, E, E, E, T, E, E, F, T, E, F, E, T, E], [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E]), ([F, E, E, E, E, T, E, T, F, E, E, F, E, E, T], [F, E, E, E, E, T, E, T, F, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_314 (And.intro z_1307 (And.intro z_620 trivial)))

theorem z_1709 : le (tf [F, E, E, E, E, T, E, T, E, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, T, E, F, E, F, T, E, E] [([F, E, E, E, E, E, T, T, E, F, E, F, T, E, E], [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E]), ([F, E, E, E, E, T, E, E, T, F, E, F, T, E, E], [F, E, E, E, E, T, E, F, T, E, E, F, T, E, E]), ([F, E, E, E, E, T, E, T, E, F, E, F, E, T, E], [F, E, E, E, E, T, E, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_315 (And.intro z_1178 (And.intro z_1708 trivial)))

theorem z_1710 : le (tf [F, E, E, E, T, E, E, F, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, T, E, F, E, E, T] [([F, E, E, E, E, T, E, F, E, T, E, F, E, E, T], [F, E, E, E, E, T, E, F, E, T, F, E, E, E, T]), ([F, E, E, E, T, E, E, F, E, E, T, F, E, E, T], [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_616 (And.intro z_489 trivial))

theorem z_1711 : le (tf [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T] [([F, E, E, E, E, T, E, T, F, E, E, F, E, E, T], [F, E, E, E, E, T, E, T, F, E, F, E, E, E, T]), ([F, E, E, E, T, E, E, E, F, T, E, F, E, E, T], [F, E, E, E, T, E, E, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_620 (And.intro z_1710 trivial))

theorem z_1712 : le (tf [F, E, E, E, T, E, E, T, E, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, F, E, F, E, T, E] [([F, E, E, E, E, T, E, T, E, F, E, F, E, T, E], [F, E, E, E, E, T, E, T, F, E, E, F, E, T, E]), ([F, E, E, E, T, E, E, E, T, F, E, F, E, T, E], [F, E, E, E, T, E, E, F, T, E, E, F, E, T, E]), ([F, E, E, E, T, E, E, T, E, F, E, F, E, E, T], [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1708 (And.intro z_1181 (And.intro z_1711 trivial)))

theorem z_1713 : le (tf [E, F, E, E, T, E, E, T, E, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, F, E, F, T, E, E] [([E, F, E, E, E, T, E, T, E, F, E, F, T, E, E], [F, E, E, E, E, T, E, T, E, F, E, F, T, E, E]), ([E, F, E, E, T, E, E, E, T, F, E, F, T, E, E], [E, F, E, E, T, E, E, F, T, E, E, F, T, E, E]), ([E, F, E, E, T, E, E, T, E, F, E, F, E, T, E], [F, E, E, E, T, E, E, T, E, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1709 (And.intro z_1182 (And.intro z_1712 trivial)))

theorem z_1714 : le (tf [F, E, E, T, E, E, E, T, E, F, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, T, E, F, E, F, E, E, T] [([F, E, E, E, T, E, E, T, E, F, E, F, E, E, T], [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T]), ([F, E, E, T, E, E, E, E, T, F, E, F, E, E, T], [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1711 (And.intro z_1322 trivial))

theorem z_1715 : le (tf [E, F, E, T, E, E, E, T, E, F, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, E, F, E, F, E, T, E] [([E, F, E, E, T, E, E, T, E, F, E, F, E, T, E], [F, E, E, E, T, E, E, T, E, F, E, F, E, T, E]), ([E, F, E, T, E, E, E, E, T, F, E, F, E, T, E], [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E]), ([E, F, E, T, E, E, E, T, E, F, E, F, E, E, T], [F, E, E, T, E, E, E, T, E, F, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1712 (And.intro z_1323 (And.intro z_1714 trivial)))

theorem z_1716 : le (tf [E, E, F, T, E, E, E, T, E, F, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, T, E, F, E, F, T, E, E] [([E, E, F, E, T, E, E, T, E, F, E, F, T, E, E], [E, F, E, E, T, E, E, T, E, F, E, F, T, E, E]), ([E, E, F, T, E, E, E, E, T, F, E, F, T, E, E], [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E]), ([E, E, F, T, E, E, E, T, E, F, E, F, E, T, E], [E, F, E, T, E, E, E, T, E, F, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1713 (And.intro z_1324 (And.intro z_1715 trivial)))

theorem z_1717 : le (tf [E, E, E, T, F, E, E, T, E, F, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, E, F, T, F, E, E, E] [([E, E, E, E, F, T, E, T, E, F, T, F, E, E, E], [E, E, E, F, E, T, E, T, E, F, T, F, E, E, E]), ([E, E, E, T, F, E, E, E, T, F, T, F, E, E, E], [E, E, E, T, F, E, E, F, T, E, T, F, E, E, E]), ([E, E, E, T, F, E, E, T, E, F, E, F, T, E, E], [E, E, F, T, E, E, E, T, E, F, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1707 (And.intro z_1325 (And.intro z_1716 trivial)))

theorem z_1718 : le (tf [E, E, E, T, E, F, E, T, T, F, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, F, E, T, T, F, E, F, E, E, E] [([E, E, E, E, T, F, E, T, T, F, E, F, E, E, E], [E, E, E, E, T, F, E, T, T, F, F, E, E, E, E]), ([E, E, E, T, E, F, E, T, E, F, T, F, E, E, E], [E, E, E, T, F, E, E, T, E, F, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1698 (And.intro z_1717 trivial))

theorem z_1719 : le (tf [E, E, E, E, T, T, F, F, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, F, F, F, E, E, E, E, E, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1720 : le (tf [E, E, E, E, T, T, F, F, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, F, F, E, F, E, E, E, T, E] [([E, E, E, E, T, T, F, F, E, F, E, E, E, E, T], [E, E, E, E, T, T, F, F, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1719 trivial)

theorem z_1721 : le (tf [E, E, E, E, T, T, F, F, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, F, F, E, E, F, E, T, E, E] [([E, E, E, E, T, T, F, F, E, E, F, E, E, T, E], [E, E, E, E, T, T, F, F, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1720 trivial)

theorem z_1722 : le (tf [E, E, E, E, T, T, F, F, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, F, F, E, E, T, F, E, E, E] [([E, E, E, E, T, T, F, F, E, E, E, F, T, E, E], [E, E, E, E, T, T, F, F, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1721 trivial)

theorem z_1723 : le (tf [E, F, E, E, E, E, T, T, F, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, E, T, F, E, E, E] [([E, F, E, E, E, E, T, E, F, T, T, F, E, E, E], [E, F, E, E, E, E, T, F, E, T, T, F, E, E, E]), ([E, F, E, E, E, E, T, T, F, E, E, F, T, E, E], [F, E, E, E, E, E, T, T, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1304 (And.intro z_315 trivial))

theorem z_1724 : le (tf [E, E, F, E, E, T, E, T, F, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, E, T, F, E, E, E] [([E, E, F, E, E, E, T, T, F, E, T, F, E, E, E], [E, F, E, E, E, E, T, T, F, E, T, F, E, E, E]), ([E, E, F, E, E, T, E, E, F, T, T, F, E, E, E], [E, E, F, E, E, T, E, F, E, T, T, F, E, E, E]), ([E, E, F, E, E, T, E, T, F, E, E, F, T, E, E], [E, E, F, E, E, T, E, T, F, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1723 (And.intro z_1309 (And.intro z_622 trivial)))

theorem z_1725 : le (tf [F, E, E, E, T, E, E, E, F, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, E, F, E, T, E] [([F, E, E, E, E, T, E, E, F, T, E, F, E, T, E], [F, E, E, E, E, T, E, F, E, T, E, F, E, T, E]), ([F, E, E, E, T, E, E, E, F, E, T, F, E, T, E], [F, E, E, E, T, E, E, F, E, E, T, F, E, T, E]), ([F, E, E, E, T, E, E, E, F, T, E, F, E, E, T], [F, E, E, E, T, E, E, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1307 (And.intro z_490 (And.intro z_1710 trivial)))

theorem z_1726 : le (tf [E, F, E, E, T, E, E, E, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, T, E, F, T, E, E] [([E, F, E, E, E, T, E, E, F, T, E, F, T, E, E], [E, F, E, E, E, T, E, F, E, T, E, F, T, E, E]), ([E, F, E, E, T, E, E, E, F, E, T, F, T, E, E], [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E]), ([E, F, E, E, T, E, E, E, F, T, E, F, E, T, E], [F, E, E, E, T, E, E, E, F, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1308 (And.intro z_491 (And.intro z_1725 trivial)))

theorem z_1727 : le (tf [E, E, F, E, T, E, E, E, F, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, F, T, T, F, E, E, E] [([E, E, F, E, E, T, E, E, F, T, T, F, E, E, E], [E, E, F, E, E, T, E, F, E, T, T, F, E, E, E]), ([E, E, F, E, T, E, E, E, F, T, E, F, T, E, E], [E, F, E, E, T, E, E, E, F, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1309 (And.intro z_1726 trivial))

theorem z_1728 : le (tf [E, F, E, E, T, E, E, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, F, E, E, F, E, T, E] [([E, F, E, E, E, T, E, T, F, E, E, F, E, T, E], [F, E, E, E, E, T, E, T, F, E, E, F, E, T, E]), ([E, F, E, E, T, E, E, E, F, T, E, F, E, T, E], [F, E, E, E, T, E, E, E, F, T, E, F, E, T, E]), ([E, F, E, E, T, E, E, T, F, E, E, F, E, E, T], [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1708 (And.intro z_1725 (And.intro z_1711 trivial)))

theorem z_1729 : le (tf [E, E, F, E, T, E, E, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, F, E, E, F, T, E, E] [([E, E, F, E, E, T, E, T, F, E, E, F, T, E, E], [E, E, F, E, E, T, E, T, F, E, F, E, T, E, E]), ([E, E, F, E, T, E, E, E, F, T, E, F, T, E, E], [E, F, E, E, T, E, E, E, F, T, E, F, T, E, E]), ([E, E, F, E, T, E, E, T, F, E, E, F, E, T, E], [E, F, E, E, T, E, E, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_622 (And.intro z_1726 (And.intro z_1728 trivial)))

theorem z_1730 : le (tf [E, E, E, F, T, E, E, T, F, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, E, E, T, F, E, T, F, E, E, E] [([E, E, E, F, E, T, E, T, F, E, T, F, E, E, E], [E, E, F, E, E, T, E, T, F, E, T, F, E, E, E]), ([E, E, E, F, T, E, E, E, F, T, T, F, E, E, E], [E, E, F, E, T, E, E, E, F, T, T, F, E, E, E]), ([E, E, E, F, T, E, E, T, F, E, E, F, T, E, E], [E, E, F, E, T, E, E, T, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1724 (And.intro z_1727 (And.intro z_1729 trivial)))

theorem z_1731 : le (tf [F, E, E, E, E, E, F, T, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, E, T, F, T, E, E] [([F, E, E, E, E, E, F, E, T, E, T, F, T, E, E], [F, E, E, E, E, F, E, E, T, E, T, F, T, E, E]), ([F, E, E, E, E, E, F, T, E, E, T, F, E, T, E], [F, E, E, E, E, F, E, T, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_275 (And.intro z_214 trivial))

theorem z_1732 : le (tf [F, E, E, E, E, F, E, T, E, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, T, E, T, E, F, E, E, T] [([F, E, E, E, E, F, E, E, T, T, E, F, E, E, T], [F, E, E, E, F, E, E, E, T, T, E, F, E, E, T]), ([F, E, E, E, E, F, E, T, E, E, T, F, E, E, T], [F, E, E, E, F, E, E, T, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_276 (And.intro z_189 trivial))

theorem z_1733 : le (tf [F, E, E, E, E, E, F, T, E, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, T, E, T, E, F, E, T, E] [([F, E, E, E, E, E, F, E, T, T, E, F, E, T, E], [F, E, E, E, E, F, E, E, T, T, E, F, E, T, E]), ([F, E, E, E, E, E, F, T, E, E, T, F, E, T, E], [F, E, E, E, E, F, E, T, E, E, T, F, E, T, E]), ([F, E, E, E, E, E, F, T, E, T, E, F, E, E, T], [F, E, E, E, E, F, E, T, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_277 (And.intro z_214 (And.intro z_1732 trivial)))

theorem z_1734 : le (tf [F, E, E, E, E, E, E, T, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, F, T, E, F, T, E, E] [([F, E, E, E, E, E, E, T, F, E, T, F, T, E, E], [F, E, E, E, E, E, F, T, E, E, T, F, T, E, E]), ([F, E, E, E, E, E, E, T, F, T, E, F, E, T, E], [F, E, E, E, E, E, F, T, E, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1731 (And.intro z_1733 trivial))

theorem z_1735 : le (tf [E, F, E, E, E, E, E, T, F, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, F, T, T, F, E, E, E] [([E, F, E, E, E, E, E, T, F, T, E, F, T, E, E], [F, E, E, E, E, E, E, T, F, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1734 trivial)

theorem z_1736 : le (tf [F, E, E, E, E, F, E, E, E, T, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, T, T, F, E, T, E] [([F, E, E, E, E, F, E, E, E, T, E, F, T, T, E], [F, E, E, E, F, E, E, E, E, T, E, F, T, T, E]), ([F, E, E, E, E, F, E, E, E, T, T, F, E, E, T], [F, E, E, E, F, E, E, E, E, T, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_43 (And.intro z_50 trivial))

theorem z_1737 : le (tf [F, E, E, E, E, E, F, E, T, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, T, E, T, F, E, T, E] [([F, E, E, E, E, E, F, E, E, T, T, F, E, T, E], [F, E, E, E, E, F, E, E, E, T, T, F, E, T, E]), ([F, E, E, E, E, E, F, E, T, E, E, F, T, T, E], [F, E, E, E, E, F, E, E, T, E, E, F, T, T, E]), ([F, E, E, E, E, E, F, E, T, E, T, F, E, E, T], [F, E, E, E, E, F, E, E, T, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1736 (And.intro z_46 (And.intro z_51 trivial)))

theorem z_1738 : le (tf [F, E, E, E, E, F, T, E, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, T, E, E, E, E, F, T, T, E] [([F, E, E, E, E, F, E, T, E, E, E, F, T, T, E], [F, E, E, E, F, E, E, T, E, E, E, F, T, T, E]), ([F, E, E, E, E, F, T, E, E, E, E, F, T, E, T], [F, E, E, E, F, E, T, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_213 (And.intro z_191 trivial))

theorem z_1739 : le (tf [F, E, E, E, E, E, T, F, E, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, F, E, E, T, F, E, T, E] [([F, E, E, E, E, E, E, F, T, E, T, F, E, T, E], [F, E, E, E, E, E, F, E, T, E, T, F, E, T, E]), ([F, E, E, E, E, E, T, F, E, E, E, F, T, T, E], [F, E, E, E, E, F, T, E, E, E, E, F, T, T, E]), ([F, E, E, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, E, F, T, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1737 (And.intro z_1738 (And.intro z_192 trivial)))

theorem z_1740 : le (tf [F, E, E, E, E, E, T, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, E, T, F, T, E, E] [([F, E, E, E, E, E, E, T, F, E, T, F, T, E, E], [F, E, E, E, E, E, F, T, E, E, T, F, T, E, E]), ([F, E, E, E, E, E, T, E, F, E, T, F, E, T, E], [F, E, E, E, E, E, T, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1731 (And.intro z_1739 trivial))

theorem z_1741 : le (tf [F, E, E, E, E, E, T, E, F, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, F, T, E, F, E, T, E] [([F, E, E, E, E, E, E, T, F, T, E, F, E, T, E], [F, E, E, E, E, E, F, T, E, T, E, F, E, T, E]), ([F, E, E, E, E, E, T, E, F, E, T, F, E, T, E], [F, E, E, E, E, E, T, F, E, E, T, F, E, T, E]), ([F, E, E, E, E, E, T, E, F, T, E, F, E, E, T], [F, E, E, E, E, E, T, F, E, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1733 (And.intro z_1739 (And.intro z_193 trivial)))

theorem z_1742 : le (tf [E, F, E, E, E, E, T, E, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, F, T, E, F, T, E, E] [([E, F, E, E, E, E, E, T, F, T, E, F, T, E, E], [F, E, E, E, E, E, E, T, F, T, E, F, T, E, E]), ([E, F, E, E, E, E, T, E, F, E, T, F, T, E, E], [F, E, E, E, E, E, T, E, F, E, T, F, T, E, E]), ([E, F, E, E, E, E, T, E, F, T, E, F, E, T, E], [F, E, E, E, E, E, T, E, F, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1734 (And.intro z_1740 (And.intro z_1741 trivial)))

theorem z_1743 : le (tf [E, E, F, E, E, E, T, E, F, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, F, T, T, F, E, E, E] [([E, E, F, E, E, E, E, T, F, T, T, F, E, E, E], [E, F, E, E, E, E, E, T, F, T, T, F, E, E, E]), ([E, E, F, E, E, E, T, E, F, T, E, F, T, E, E], [E, F, E, E, E, E, T, E, F, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1735 (And.intro z_1742 trivial))

theorem z_1744 : le (tf [F, E, E, E, F, T, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, T, E, E, E, E, E, F, E, T, T] [([F, E, E, E, F, E, T, E, E, E, E, F, E, T, T], [F, E, E, F, E, E, T, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_190 trivial)

theorem z_1745 : le (tf [F, E, E, E, E, T, F, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, F, E, E, E, E, F, T, E, T] [([F, E, E, E, E, E, F, T, E, E, E, F, T, E, T], [F, E, E, E, E, F, E, T, E, E, E, F, T, E, T]), ([F, E, E, E, E, T, F, E, E, E, E, F, E, T, T], [F, E, E, E, F, T, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_1744 trivial))

theorem z_1746 : le (tf [F, E, E, E, E, T, E, F, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, E, F, T, T, E] [([F, E, E, E, E, E, T, F, E, E, E, F, T, T, E], [F, E, E, E, E, F, T, E, E, E, E, F, T, T, E]), ([F, E, E, E, E, T, E, F, E, E, E, F, T, E, T], [F, E, E, E, E, T, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1738 (And.intro z_1745 trivial))

theorem z_1747 : le (tf [F, E, E, E, E, T, E, F, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, F, E, E, T, F, E, E, T] [([F, E, E, E, E, E, T, F, E, E, T, F, E, E, T], [F, E, E, E, E, F, T, E, E, E, T, F, E, E, T]), ([F, E, E, E, E, T, E, F, E, E, E, F, T, E, T], [F, E, E, E, E, T, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_192 (And.intro z_1745 trivial))

theorem z_1748 : le (tf [F, E, E, E, E, T, E, E, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, E, T, F, E, T, E] [([F, E, E, E, E, E, T, E, F, E, T, F, E, T, E], [F, E, E, E, E, E, T, F, E, E, T, F, E, T, E]), ([F, E, E, E, E, T, E, E, F, E, E, F, T, T, E], [F, E, E, E, E, T, E, F, E, E, E, F, T, T, E]), ([F, E, E, E, E, T, E, E, F, E, T, F, E, E, T], [F, E, E, E, E, T, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1739 (And.intro z_1746 (And.intro z_1747 trivial)))

theorem z_1749 : le (tf [E, F, E, E, E, T, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, F, E, T, F, T, E, E] [([E, F, E, E, E, E, T, E, F, E, T, F, T, E, E], [F, E, E, E, E, E, T, E, F, E, T, F, T, E, E]), ([E, F, E, E, E, T, E, E, F, E, T, F, E, T, E], [F, E, E, E, E, T, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1740 (And.intro z_1748 trivial))

theorem z_1750 : le (tf [F, E, E, E, E, T, E, E, F, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, F, T, E, F, E, E, T] [([F, E, E, E, E, E, T, E, F, T, E, F, E, E, T], [F, E, E, E, E, E, T, F, E, T, E, F, E, E, T]), ([F, E, E, E, E, T, E, E, F, E, T, F, E, E, T], [F, E, E, E, E, T, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_193 (And.intro z_1747 trivial))

theorem z_1751 : le (tf [E, F, E, E, E, T, E, E, F, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, F, T, E, F, E, T, E] [([E, F, E, E, E, E, T, E, F, T, E, F, E, T, E], [F, E, E, E, E, E, T, E, F, T, E, F, E, T, E]), ([E, F, E, E, E, T, E, E, F, E, T, F, E, T, E], [F, E, E, E, E, T, E, E, F, E, T, F, E, T, E]), ([E, F, E, E, E, T, E, E, F, T, E, F, E, E, T], [F, E, E, E, E, T, E, E, F, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1741 (And.intro z_1748 (And.intro z_1750 trivial)))

theorem z_1752 : le (tf [E, E, F, E, E, T, E, E, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, F, T, E, F, T, E, E] [([E, E, F, E, E, E, T, E, F, T, E, F, T, E, E], [E, F, E, E, E, E, T, E, F, T, E, F, T, E, E]), ([E, E, F, E, E, T, E, E, F, E, T, F, T, E, E], [E, F, E, E, E, T, E, E, F, E, T, F, T, E, E]), ([E, E, F, E, E, T, E, E, F, T, E, F, E, T, E], [E, F, E, E, E, T, E, E, F, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1742 (And.intro z_1749 (And.intro z_1751 trivial)))

theorem z_1753 : le (tf [E, E, E, F, E, T, E, E, F, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, E, F, T, T, F, E, E, E] [([E, E, E, F, E, E, T, E, F, T, T, F, E, E, E], [E, E, F, E, E, E, T, E, F, T, T, F, E, E, E]), ([E, E, E, F, E, T, E, E, F, T, E, F, T, E, E], [E, E, F, E, E, T, E, E, F, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1743 (And.intro z_1752 trivial))

theorem z_1754 : le (tf [E, F, E, T, E, E, E, E, F, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, E, T, F, T, E, E] [([E, F, E, E, T, E, E, E, F, E, T, F, T, E, E], [F, E, E, E, T, E, E, E, F, E, T, F, T, E, E]), ([E, F, E, T, E, E, E, E, F, E, T, F, E, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_491 (And.intro z_505 trivial))

theorem z_1755 : le (tf [F, E, E, T, E, E, E, E, F, T, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, E, E, F, T, E, F, E, E, T] [([F, E, E, E, T, E, E, E, F, T, E, F, E, E, T], [F, E, E, E, T, E, E, F, E, T, E, F, E, E, T]), ([F, E, E, T, E, E, E, E, F, E, T, F, E, E, T], [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1710 (And.intro z_504 trivial))

theorem z_1756 : le (tf [E, F, E, T, E, E, E, E, F, T, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, T, E, F, E, T, E] [([E, F, E, E, T, E, E, E, F, T, E, F, E, T, E], [F, E, E, E, T, E, E, E, F, T, E, F, E, T, E]), ([E, F, E, T, E, E, E, E, F, E, T, F, E, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E]), ([E, F, E, T, E, E, E, E, F, T, E, F, E, E, T], [F, E, E, T, E, E, E, E, F, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1725 (And.intro z_505 (And.intro z_1755 trivial)))

theorem z_1757 : le (tf [E, E, F, T, E, E, E, E, F, T, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, E, F, T, E, F, T, E, E] [([E, E, F, E, T, E, E, E, F, T, E, F, T, E, E], [E, F, E, E, T, E, E, E, F, T, E, F, T, E, E]), ([E, E, F, T, E, E, E, E, F, E, T, F, T, E, E], [E, F, E, T, E, E, E, E, F, E, T, F, T, E, E]), ([E, E, F, T, E, E, E, E, F, T, E, F, E, T, E], [E, F, E, T, E, E, E, E, F, T, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1726 (And.intro z_1754 (And.intro z_1756 trivial)))

theorem z_1758 : le (tf [E, E, E, T, F, E, E, E, F, T, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, E, F, T, T, F, E, E, E] [([E, E, E, E, F, T, E, E, F, T, T, F, E, E, E], [E, E, E, F, E, T, E, E, F, T, T, F, E, E, E]), ([E, E, E, T, F, E, E, E, F, T, E, F, T, E, E], [E, E, F, T, E, E, E, E, F, T, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1753 (And.intro z_1757 trivial))

theorem z_1759 : le (tf [E, F, E, E, E, E, T, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, T, F, E, E, F, E, T, E] [([E, F, E, E, E, E, T, E, F, T, E, F, E, T, E], [F, E, E, E, E, E, T, E, F, T, E, F, E, T, E]), ([E, F, E, E, E, E, T, T, F, E, E, F, E, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1741 (And.intro z_194 trivial))

theorem z_1760 : le (tf [E, E, F, E, E, E, T, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, T, F, E, E, F, T, E, E] [([E, E, F, E, E, E, T, E, F, T, E, F, T, E, E], [E, F, E, E, E, E, T, E, F, T, E, F, T, E, E]), ([E, E, F, E, E, E, T, T, F, E, E, F, E, T, E], [E, F, E, E, E, E, T, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1742 (And.intro z_1759 trivial))

theorem z_1761 : le (tf [E, F, E, E, E, T, E, T, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, T, F, E, E, F, E, E, T] [([E, F, E, E, E, E, T, T, F, E, E, F, E, E, T], [F, E, E, E, E, E, T, T, F, E, E, F, E, E, T]), ([E, F, E, E, E, T, E, E, F, T, E, F, E, E, T], [F, E, E, E, E, T, E, E, F, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 (And.intro z_1750 trivial))

theorem z_1762 : le (tf [E, E, F, E, E, T, E, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, T, F, E, E, F, E, T, E] [([E, E, F, E, E, E, T, T, F, E, E, F, E, T, E], [E, F, E, E, E, E, T, T, F, E, E, F, E, T, E]), ([E, E, F, E, E, T, E, E, F, T, E, F, E, T, E], [E, F, E, E, E, T, E, E, F, T, E, F, E, T, E]), ([E, E, F, E, E, T, E, T, F, E, E, F, E, E, T], [E, F, E, E, E, T, E, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1759 (And.intro z_1751 (And.intro z_1761 trivial)))

theorem z_1763 : le (tf [E, E, E, F, E, T, E, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, T, F, E, E, F, T, E, E] [([E, E, E, F, E, E, T, T, F, E, E, F, T, E, E], [E, E, F, E, E, E, T, T, F, E, E, F, T, E, E]), ([E, E, E, F, E, T, E, E, F, T, E, F, T, E, E], [E, E, F, E, E, T, E, E, F, T, E, F, T, E, E]), ([E, E, E, F, E, T, E, T, F, E, E, F, E, T, E], [E, E, F, E, E, T, E, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1760 (And.intro z_1752 (And.intro z_1762 trivial)))

theorem z_1764 : le (tf [E, F, E, T, E, E, E, T, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, F, E, E, F, E, E, T] [([E, F, E, E, T, E, E, T, F, E, E, F, E, E, T], [F, E, E, E, T, E, E, T, F, E, E, F, E, E, T]), ([E, F, E, T, E, E, E, E, F, T, E, F, E, E, T], [F, E, E, T, E, E, E, E, F, T, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1711 (And.intro z_1755 trivial))

theorem z_1765 : le (tf [E, E, F, T, E, E, E, T, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, T, F, E, E, F, E, T, E] [([E, E, F, E, T, E, E, T, F, E, E, F, E, T, E], [E, F, E, E, T, E, E, T, F, E, E, F, E, T, E]), ([E, E, F, T, E, E, E, E, F, T, E, F, E, T, E], [E, F, E, T, E, E, E, E, F, T, E, F, E, T, E]), ([E, E, F, T, E, E, E, T, F, E, E, F, E, E, T], [E, F, E, T, E, E, E, T, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1728 (And.intro z_1756 (And.intro z_1764 trivial)))

theorem z_1766 : le (tf [E, E, E, T, F, E, E, T, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, T, F, E, E, F, T, E, E] [([E, E, E, E, F, T, E, T, F, E, E, F, T, E, E], [E, E, E, F, E, T, E, T, F, E, E, F, T, E, E]), ([E, E, E, T, F, E, E, E, F, T, E, F, T, E, E], [E, E, F, T, E, E, E, E, F, T, E, F, T, E, E]), ([E, E, E, T, F, E, E, T, F, E, E, F, E, T, E], [E, E, F, T, E, E, E, T, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1763 (And.intro z_1757 (And.intro z_1765 trivial)))

theorem z_1767 : le (tf [E, E, E, T, E, F, E, T, F, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, F, E, T, F, E, T, F, E, E, E] [([E, E, E, E, T, F, E, T, F, E, T, F, E, E, E], [E, E, E, F, T, E, E, T, F, E, T, F, E, E, E]), ([E, E, E, T, E, F, E, E, F, T, T, F, E, E, E], [E, E, E, T, F, E, E, E, F, T, T, F, E, E, E]), ([E, E, E, T, E, F, E, T, F, E, E, F, T, E, E], [E, E, E, T, F, E, E, T, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1730 (And.intro z_1758 (And.intro z_1766 trivial)))

theorem z_1768 : le (tf [E, F, E, E, E, T, T, F, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, T, F, E, E, E, F, E, E, T] [([E, F, E, E, E, T, E, F, T, E, E, F, E, E, T], [F, E, E, E, E, T, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1310 trivial)

theorem z_1769 : le (tf [E, E, F, E, E, T, T, F, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, T, F, E, E, E, F, E, T, E] [([E, E, F, E, E, T, E, F, T, E, E, F, E, T, E], [E, F, E, E, E, T, E, F, T, E, E, F, E, T, E]), ([E, E, F, E, E, T, T, F, E, E, E, F, E, E, T], [E, F, E, E, E, T, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1311 (And.intro z_1768 trivial))

theorem z_1770 : le (tf [E, E, E, F, E, T, T, F, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, T, F, E, E, E, F, T, E, E] [([E, E, E, F, E, T, E, F, T, E, E, F, T, E, E], [E, E, F, E, E, T, E, F, T, E, E, F, T, E, E]), ([E, E, E, F, E, T, T, F, E, E, E, F, E, T, E], [E, E, F, E, E, T, T, F, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1312 (And.intro z_1769 trivial))

theorem z_1771 : le (tf [E, F, E, T, E, E, T, F, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, E, F, E, E, T] [([E, F, E, E, T, E, T, F, E, E, E, F, E, E, T], [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T]), ([E, F, E, T, E, E, E, F, T, E, E, F, E, E, T], [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_755 (And.intro z_1322 trivial))

theorem z_1772 : le (tf [E, E, F, T, E, E, T, F, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, T, F, E, E, E, F, E, T, E] [([E, E, F, E, T, E, T, F, E, E, E, F, E, T, E], [E, F, E, E, T, E, T, F, E, E, E, F, E, T, E]), ([E, E, F, T, E, E, E, F, T, E, E, F, E, T, E], [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E]), ([E, E, F, T, E, E, T, F, E, E, E, F, E, E, T], [E, F, E, T, E, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1183 (And.intro z_1323 (And.intro z_1771 trivial)))

theorem z_1773 : le (tf [E, E, E, T, F, E, T, F, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, T, F, E, E, E, F, T, E, E] [([E, E, E, E, F, T, T, F, E, E, E, F, T, E, E], [E, E, E, F, E, T, T, F, E, E, E, F, T, E, E]), ([E, E, E, T, F, E, E, F, T, E, E, F, T, E, E], [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E]), ([E, E, E, T, F, E, T, F, E, E, E, F, E, T, E], [E, E, F, T, E, E, T, F, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1770 (And.intro z_1324 (And.intro z_1772 trivial)))

theorem z_1774 : le (tf [F, E, E, E, T, T, E, E, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, T, E, E, F, E, E, F, E, E, T] [([F, E, E, E, T, E, T, E, F, E, E, F, E, E, T], [F, E, E, E, T, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_755 trivial)

theorem z_1775 : le (tf [E, F, E, E, T, T, E, E, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, E, E, F, E, T, E] [([E, F, E, E, T, E, T, E, F, E, E, F, E, T, E], [E, F, E, E, T, E, T, F, E, E, E, F, E, T, E]), ([E, F, E, E, T, T, E, E, F, E, E, F, E, E, T], [F, E, E, E, T, T, E, E, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1183 (And.intro z_1774 trivial))

theorem z_1776 : le (tf [E, F, E, T, E, T, E, E, F, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, F, E, E, F, E, E, T] [([E, F, E, E, T, T, E, E, F, E, E, F, E, E, T], [F, E, E, E, T, T, E, E, F, E, E, F, E, E, T]), ([E, F, E, T, E, E, T, E, F, E, E, F, E, E, T], [E, F, E, T, E, E, T, F, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1774 (And.intro z_1771 trivial))

theorem z_1777 : le (tf [E, E, F, T, E, T, E, E, F, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, T, E, E, F, E, E, F, E, T, E] [([E, E, F, E, T, T, E, E, F, E, E, F, E, T, E], [E, F, E, E, T, T, E, E, F, E, E, F, E, T, E]), ([E, E, F, T, E, E, T, E, F, E, E, F, E, T, E], [E, E, F, T, E, E, T, F, E, E, E, F, E, T, E]), ([E, E, F, T, E, T, E, E, F, E, E, F, E, E, T], [E, F, E, T, E, T, E, E, F, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1775 (And.intro z_1772 (And.intro z_1776 trivial)))

theorem z_1778 : le (tf [E, E, E, T, F, T, E, E, F, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, T, E, E, F, E, E, F, T, E, E] [([E, E, E, T, F, E, T, E, F, E, E, F, T, E, E], [E, E, E, T, F, E, T, F, E, E, E, F, T, E, E]), ([E, E, E, T, F, T, E, E, F, E, E, F, E, T, E], [E, E, F, T, E, T, E, E, F, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1773 (And.intro z_1777 trivial))

theorem z_1779 : le (tf [E, E, E, T, E, T, F, E, F, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, T, F, E, F, E, T, F, E, E, E] [([E, E, E, E, T, T, F, E, F, E, T, F, E, E, E], [E, E, E, E, T, T, F, F, E, E, T, F, E, E, E]), ([E, E, E, T, E, E, F, T, F, E, T, F, E, E, E], [E, E, E, T, E, F, E, T, F, E, T, F, E, E, E]), ([E, E, E, T, E, T, F, E, F, E, E, F, T, E, E], [E, E, E, T, F, T, E, E, F, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1722 (And.intro z_1767 (And.intro z_1778 trivial)))

theorem z_1780 : le (tf [E, E, E, T, E, T, F, E, T, F, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, T, F, E, T, F, E, F, E, E, E] [([E, E, E, E, T, T, F, E, T, F, E, F, E, E, E], [E, E, E, E, T, T, F, E, T, F, F, E, E, E, E]), ([E, E, E, T, E, E, F, T, T, F, E, F, E, E, E], [E, E, E, T, E, F, E, T, T, F, E, F, E, E, E]), ([E, E, E, T, E, T, F, E, E, F, T, F, E, E, E], [E, E, E, T, E, T, F, E, F, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1699 (And.intro z_1718 (And.intro z_1779 trivial)))

theorem z_1781 : le (tf [F, E, E, E, T, E, E, F, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, E, E, T, E, F, E, T] [([F, E, E, E, E, T, E, F, E, E, T, E, F, E, T], [F, E, E, E, E, T, F, E, E, E, T, E, F, E, T]), ([F, E, E, E, T, E, E, F, E, E, E, T, F, E, T], [F, E, E, E, T, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_571 (And.intro z_777 trivial))

theorem z_1782 : le (tf [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E] [([F, E, E, E, E, T, E, E, F, E, T, E, F, T, E], [F, E, E, E, E, T, E, F, E, E, T, E, F, T, E]), ([F, E, E, E, T, E, E, E, F, E, E, T, F, T, E], [F, E, E, E, T, E, E, F, E, E, E, T, F, T, E]), ([F, E, E, E, T, E, E, E, F, E, T, E, F, E, T], [F, E, E, E, T, E, E, F, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_572 (And.intro z_778 (And.intro z_1781 trivial)))

theorem z_1783 : le (tf [F, E, E, E, T, E, E, E, E, F, T, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, E, F, T, T, F, E, E] [([F, E, E, E, E, T, E, E, E, F, T, T, F, E, E], [F, E, E, E, E, T, E, E, F, E, T, T, F, E, E]), ([F, E, E, E, T, E, E, E, E, F, T, E, F, T, E], [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_573 (And.intro z_1782 trivial))

theorem z_1784 : le (tf [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T] [([F, E, E, E, E, T, E, F, T, E, E, E, F, E, T], [F, E, E, E, E, T, F, E, T, E, E, E, F, E, T]), ([F, E, E, E, T, E, E, F, E, T, E, E, F, E, T], [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_746 (And.intro z_587 trivial))

theorem z_1785 : le (tf [F, E, E, E, T, E, E, E, T, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, T, F, E, E, F, T, E] [([F, E, E, E, E, T, E, E, T, F, E, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E]), ([F, E, E, E, T, E, E, E, E, F, T, E, F, T, E], [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E]), ([F, E, E, E, T, E, E, E, T, F, E, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1299 (And.intro z_1782 (And.intro z_1784 trivial)))

theorem z_1786 : le (tf [E, F, E, E, T, E, E, E, T, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, T, F, E, T, F, E, E] [([E, F, E, E, E, T, E, E, T, F, E, T, F, E, E], [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E]), ([E, F, E, E, T, E, E, E, E, F, T, T, F, E, E], [F, E, E, E, T, E, E, E, E, F, T, T, F, E, E]), ([E, F, E, E, T, E, E, E, T, F, E, E, F, T, E], [F, E, E, E, T, E, E, E, T, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1300 (And.intro z_1783 (And.intro z_1785 trivial)))

theorem z_1787 : le (tf [E, E, F, E, T, E, E, E, T, F, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, T, F, T, E, F, E, E] [([E, E, F, E, E, T, E, E, T, F, T, E, F, E, E], [E, E, F, E, E, T, E, F, T, E, T, E, F, E, E]), ([E, E, F, E, T, E, E, E, T, F, E, T, F, E, E], [E, F, E, E, T, E, E, E, T, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1301 (And.intro z_1786 trivial))

theorem z_1788 : le (tf [E, F, E, E, T, E, E, F, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, E, T, E, T, F, E, E] [([E, F, E, E, E, T, E, F, E, T, E, T, F, E, E], [F, E, E, E, E, T, E, F, E, T, E, T, F, E, E]), ([E, F, E, E, T, E, E, F, E, E, T, T, F, E, E], [F, E, E, E, T, E, E, F, E, E, T, T, F, E, E]), ([E, F, E, E, T, E, E, F, E, T, E, E, F, T, E], [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_584 (And.intro z_586 (And.intro z_588 trivial)))

theorem z_1789 : le (tf [E, F, E, E, T, E, E, F, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, F, T, E, E, E, F, T, E] [([E, F, E, E, E, T, E, F, T, E, E, E, F, T, E], [F, E, E, E, E, T, E, F, T, E, E, E, F, T, E]), ([E, F, E, E, T, E, E, F, E, T, E, E, F, T, E], [F, E, E, E, T, E, E, F, E, T, E, E, F, T, E]), ([E, F, E, E, T, E, E, F, T, E, E, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1299 (And.intro z_588 (And.intro z_1784 trivial)))

theorem z_1790 : le (tf [E, E, F, E, T, E, E, F, T, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, F, T, E, E, T, F, E, E] [([E, E, F, E, E, T, E, F, T, E, E, T, F, E, E], [E, F, E, E, E, T, E, F, T, E, E, T, F, E, E]), ([E, E, F, E, T, E, E, F, E, T, E, T, F, E, E], [E, F, E, E, T, E, E, F, E, T, E, T, F, E, E]), ([E, E, F, E, T, E, E, F, T, E, E, E, F, T, E], [E, F, E, E, T, E, E, F, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1300 (And.intro z_1788 (And.intro z_1789 trivial)))

theorem z_1791 : le (tf [E, F, E, E, E, T, F, E, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, E, E, T, E, T, F, E, E] [([E, F, E, E, E, E, F, T, E, T, E, T, F, E, E], [F, E, E, E, E, E, F, T, E, T, E, T, F, E, E]), ([E, F, E, E, E, T, F, E, E, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([E, F, E, E, E, T, F, E, E, T, E, E, F, T, E], [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_562 (And.intro z_355 (And.intro z_583 trivial)))

theorem z_1792 : le (tf [F, E, E, E, T, E, F, E, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, F, E, E, E, T, E, F, T, E] [([F, E, E, E, E, T, F, E, E, E, T, E, F, T, E], [F, E, E, E, E, T, F, E, E, E, T, F, E, T, E]), ([F, E, E, E, T, E, F, E, E, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E]), ([F, E, E, E, T, E, F, E, E, E, T, E, F, E, T], [F, E, E, E, T, E, F, E, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_219 (And.intro z_529 (And.intro z_489 trivial)))

theorem z_1793 : le (tf [E, F, E, E, T, E, F, E, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, E, T, T, F, E, E] [([E, F, E, E, E, T, F, E, E, E, T, T, F, E, E], [F, E, E, E, E, T, F, E, E, E, T, T, F, E, E]), ([E, F, E, E, T, E, F, E, E, E, T, E, F, T, E], [F, E, E, E, T, E, F, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_1792 trivial))

theorem z_1794 : le (tf [E, F, E, E, T, E, F, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, T, E, E, F, T, E] [([E, F, E, E, E, T, F, E, E, T, E, E, F, T, E], [F, E, E, E, E, T, F, E, E, T, E, E, F, T, E]), ([E, F, E, E, T, E, F, E, E, E, T, E, F, T, E], [F, E, E, E, T, E, F, E, E, E, T, E, F, T, E]), ([E, F, E, E, T, E, F, E, E, T, E, E, F, E, T], [F, E, E, E, T, E, F, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_583 (And.intro z_1792 (And.intro z_587 trivial)))

theorem z_1795 : le (tf [E, E, F, E, T, E, F, E, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, E, E, T, E, T, F, E, E] [([E, E, F, E, E, T, F, E, E, T, E, T, F, E, E], [E, F, E, E, E, T, F, E, E, T, E, T, F, E, E]), ([E, E, F, E, T, E, F, E, E, E, T, T, F, E, E], [E, F, E, E, T, E, F, E, E, E, T, T, F, E, E]), ([E, E, F, E, T, E, F, E, E, T, E, E, F, T, E], [E, F, E, E, T, E, F, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1791 (And.intro z_1793 (And.intro z_1794 trivial)))

theorem z_1796 : le (tf [E, F, E, E, E, F, T, E, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, F, T, E, E, E, T, T, F, E, E] [([E, F, E, E, E, F, E, T, E, E, T, T, F, E, E], [F, E, E, E, E, F, E, T, E, E, T, T, F, E, E]), ([E, F, E, E, E, F, T, E, E, E, T, E, F, T, E], [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_354 (And.intro z_178 trivial))

theorem z_1797 : le (tf [F, E, E, E, T, F, E, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, F, E, E, E, E, T, E, F, E, T] [([F, E, E, E, E, F, T, E, E, E, T, E, F, E, T], [F, E, E, E, F, E, T, E, E, E, T, E, F, E, T]), ([F, E, E, E, T, F, E, E, E, E, E, T, F, E, T], [F, E, E, F, T, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_177 (And.intro z_528 trivial))

theorem z_1798 : le (tf [E, F, E, E, T, F, E, E, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, E, T, E, F, T, E] [([E, F, E, E, E, F, T, E, E, E, T, E, F, T, E], [F, E, E, E, E, F, T, E, E, E, T, E, F, T, E]), ([E, F, E, E, T, F, E, E, E, E, E, T, F, T, E], [F, E, E, E, T, F, E, E, E, E, E, T, F, T, E]), ([E, F, E, E, T, F, E, E, E, E, T, E, F, E, T], [F, E, E, E, T, F, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 (And.intro z_529 (And.intro z_1797 trivial)))

theorem z_1799 : le (tf [E, E, F, E, T, F, E, E, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, F, E, E, E, E, T, T, F, E, E] [([E, E, F, E, E, F, T, E, E, E, T, T, F, E, E], [E, F, E, E, E, F, T, E, E, E, T, T, F, E, E]), ([E, E, F, E, T, F, E, E, E, E, T, E, F, T, E], [E, F, E, E, T, F, E, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1796 (And.intro z_1798 trivial))

theorem z_1800 : le (tf [F, E, T, E, E, F, E, E, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, F, E, E, E, E, T, E, F, E, T] [([F, E, E, T, E, F, E, E, E, E, T, E, F, E, T], [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T]), ([F, E, T, E, E, F, E, E, E, E, E, T, F, E, T], [F, E, T, E, F, E, E, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_906 (And.intro z_849 trivial))

theorem z_1801 : le (tf [E, F, T, E, E, F, E, E, E, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, F, E, E, E, E, T, E, F, T, E] [([E, F, E, T, E, F, E, E, E, E, T, E, F, T, E], [E, F, E, T, E, F, E, E, E, E, T, F, E, T, E]), ([E, F, T, E, E, F, E, E, E, E, E, T, F, T, E], [F, E, T, E, E, F, E, E, E, E, E, T, F, T, E]), ([E, F, T, E, E, F, E, E, E, E, T, E, F, E, T], [F, E, T, E, E, F, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1041 (And.intro z_850 (And.intro z_1800 trivial)))

theorem z_1802 : le (tf [E, E, T, F, E, F, E, E, E, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, F, E, E, E, E, T, T, F, E, E] [([E, E, E, F, T, F, E, E, E, E, T, T, F, E, E], [E, E, F, E, T, F, E, E, E, E, T, T, F, E, E]), ([E, E, T, F, E, F, E, E, E, E, T, E, F, T, E], [E, F, T, E, E, F, E, E, E, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1799 (And.intro z_1801 trivial))

theorem z_1803 : le (tf [F, E, E, T, E, F, E, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, T, E, F, E, E, E, T, E, E, F, E, T] [([F, E, E, E, T, F, E, E, E, T, E, E, F, E, T], [F, E, E, E, T, F, E, E, E, T, E, F, E, E, T]), ([F, E, E, T, E, F, E, E, E, E, T, E, F, E, T], [F, E, E, T, F, E, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_906 trivial))

theorem z_1804 : le (tf [F, E, E, T, E, E, F, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, T, E, E, F, E, E, T, E, E, F, T, E] [([F, E, E, E, T, E, F, E, E, T, E, E, F, T, E], [F, E, E, E, T, F, E, E, E, T, E, E, F, T, E]), ([F, E, E, T, E, E, F, E, E, E, T, E, F, T, E], [F, E, E, T, E, E, F, E, E, E, T, F, E, T, E]), ([F, E, E, T, E, E, F, E, E, T, E, E, F, E, T], [F, E, E, T, E, F, E, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_481 (And.intro z_512 (And.intro z_1803 trivial)))

theorem z_1805 : le (tf [F, E, T, E, E, E, F, E, E, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, F, E, E, T, E, E, F, E, T] [([F, E, E, T, E, E, F, E, E, T, E, E, F, E, T], [F, E, E, T, E, F, E, E, E, T, E, E, F, E, T]), ([F, E, T, E, E, E, F, E, E, E, T, E, F, E, T], [F, E, T, E, E, F, E, E, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1803 (And.intro z_1800 trivial))

theorem z_1806 : le (tf [E, F, T, E, E, E, F, E, E, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, E, E, T, E, E, F, T, E] [([E, F, E, T, E, E, F, E, E, T, E, E, F, T, E], [F, E, E, T, E, E, F, E, E, T, E, E, F, T, E]), ([E, F, T, E, E, E, F, E, E, E, T, E, F, T, E], [E, F, T, E, E, F, E, E, E, E, T, E, F, T, E]), ([E, F, T, E, E, E, F, E, E, T, E, E, F, E, T], [F, E, T, E, E, E, F, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1804 (And.intro z_1801 (And.intro z_1805 trivial)))

theorem z_1807 : le (tf [E, E, T, F, E, E, F, E, E, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, E, E, T, E, T, F, E, E] [([E, E, E, F, T, E, F, E, E, T, E, T, F, E, E], [E, E, F, E, T, E, F, E, E, T, E, T, F, E, E]), ([E, E, T, F, E, E, F, E, E, E, T, T, F, E, E], [E, E, T, F, E, F, E, E, E, E, T, T, F, E, E]), ([E, E, T, F, E, E, F, E, E, T, E, E, F, T, E], [E, F, T, E, E, E, F, E, E, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1795 (And.intro z_1802 (And.intro z_1806 trivial)))

theorem z_1808 : le (tf [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T] [([F, E, E, T, E, E, E, F, T, E, E, E, F, E, T], [F, E, E, T, E, E, E, F, T, E, E, F, E, E, T]), ([F, E, T, E, E, E, E, F, E, T, E, E, F, E, T], [F, E, T, E, E, E, F, E, E, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1322 (And.intro z_1805 trivial))

theorem z_1809 : le (tf [E, F, T, E, E, E, E, F, T, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, F, T, E, E, E, F, T, E] [([E, F, E, T, E, E, E, F, T, E, E, E, F, T, E], [E, F, E, T, E, E, E, F, T, E, E, F, E, T, E]), ([E, F, T, E, E, E, E, F, E, T, E, E, F, T, E], [E, F, T, E, E, E, F, E, E, T, E, E, F, T, E]), ([E, F, T, E, E, E, E, F, T, E, E, E, F, E, T], [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1323 (And.intro z_1806 (And.intro z_1808 trivial)))

theorem z_1810 : le (tf [E, E, T, F, E, E, E, F, T, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, F, T, E, E, T, F, E, E] [([E, E, E, F, T, E, E, F, T, E, E, T, F, E, E], [E, E, F, E, T, E, E, F, T, E, E, T, F, E, E]), ([E, E, T, F, E, E, E, F, E, T, E, T, F, E, E], [E, E, T, F, E, E, F, E, E, T, E, T, F, E, E]), ([E, E, T, F, E, E, E, F, T, E, E, E, F, T, E], [E, F, T, E, E, E, E, F, T, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1790 (And.intro z_1807 (And.intro z_1809 trivial)))

theorem z_1811 : le (tf [E, E, T, F, E, E, E, E, T, F, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, T, F, T, E, F, E, E] [([E, E, E, F, T, E, E, E, T, F, T, E, F, E, E], [E, E, F, E, T, E, E, E, T, F, T, E, F, E, E]), ([E, E, T, F, E, E, E, E, T, F, E, T, F, E, E], [E, E, T, F, E, E, E, F, T, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1787 (And.intro z_1810 trivial))

theorem z_1812 : le (tf [F, E, E, E, T, E, E, T, E, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, T, E, F, E, E, F, E, T] [([F, E, E, E, E, T, E, T, E, F, E, E, F, E, T], [F, E, E, E, E, T, E, T, F, E, E, E, F, E, T]), ([F, E, E, E, T, E, E, E, T, F, E, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_578 (And.intro z_1784 trivial))

theorem z_1813 : le (tf [E, F, E, E, T, E, E, T, E, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, E, F, E, E, F, T, E] [([E, F, E, E, E, T, E, T, E, F, E, E, F, T, E], [E, F, E, E, E, T, E, T, F, E, E, E, F, T, E]), ([E, F, E, E, T, E, E, E, T, F, E, E, F, T, E], [F, E, E, E, T, E, E, E, T, F, E, E, F, T, E]), ([E, F, E, E, T, E, E, T, E, F, E, E, F, E, T], [F, E, E, E, T, E, E, T, E, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_579 (And.intro z_1785 (And.intro z_1812 trivial)))

theorem z_1814 : le (tf [E, E, F, E, T, E, E, T, E, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, E, F, E, T, F, E, E] [([E, E, F, E, E, T, E, T, E, F, E, T, F, E, E], [E, E, F, E, E, T, E, T, F, E, E, T, F, E, E]), ([E, E, F, E, T, E, E, E, T, F, E, T, F, E, E], [E, F, E, E, T, E, E, E, T, F, E, T, F, E, E]), ([E, E, F, E, T, E, E, T, E, F, E, E, F, T, E], [E, F, E, E, T, E, E, T, E, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_580 (And.intro z_1786 (And.intro z_1813 trivial)))

theorem z_1815 : le (tf [F, E, T, E, E, E, E, T, E, F, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, T, E, F, E, E, F, E, T] [([F, E, E, T, E, E, E, T, E, F, E, E, F, E, T], [F, E, E, T, E, E, E, T, E, F, E, F, E, E, T]), ([F, E, T, E, E, E, E, E, T, F, E, E, F, E, T], [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1714 (And.intro z_1808 trivial))

theorem z_1816 : le (tf [E, F, T, E, E, E, E, T, E, F, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, T, E, F, E, E, F, T, E] [([E, F, E, T, E, E, E, T, E, F, E, E, F, T, E], [E, F, E, T, E, E, E, T, E, F, E, F, E, T, E]), ([E, F, T, E, E, E, E, E, T, F, E, E, F, T, E], [E, F, T, E, E, E, E, F, T, E, E, E, F, T, E]), ([E, F, T, E, E, E, E, T, E, F, E, E, F, E, T], [F, E, T, E, E, E, E, T, E, F, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1715 (And.intro z_1809 (And.intro z_1815 trivial)))

theorem z_1817 : le (tf [E, E, T, F, E, E, E, T, E, F, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, E, F, E, T, F, E, E] [([E, E, E, F, T, E, E, T, E, F, E, T, F, E, E], [E, E, F, E, T, E, E, T, E, F, E, T, F, E, E]), ([E, E, T, F, E, E, E, E, T, F, E, T, F, E, E], [E, E, T, F, E, E, E, F, T, E, E, T, F, E, E]), ([E, E, T, F, E, E, E, T, E, F, E, E, F, T, E], [E, F, T, E, E, E, E, T, E, F, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1814 (And.intro z_1810 (And.intro z_1816 trivial)))

theorem z_1818 : le (tf [E, E, T, E, F, E, E, T, E, F, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, T, E, F, T, E, F, E, E] [([E, E, E, T, F, E, E, T, E, F, T, E, F, E, E], [E, E, E, T, F, E, E, T, F, E, T, E, F, E, E]), ([E, E, T, E, F, E, E, E, T, F, T, E, F, E, E], [E, E, T, F, E, E, E, E, T, F, T, E, F, E, E]), ([E, E, T, E, F, E, E, T, E, F, E, T, F, E, E], [E, E, T, F, E, E, E, T, E, F, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_728 (And.intro z_1811 (And.intro z_1817 trivial)))

theorem z_1819 : le (tf [E, E, T, E, E, F, E, T, T, F, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, F, E, T, T, F, E, E, F, E, E] [([E, E, E, T, E, F, E, T, T, F, E, E, F, E, E], [E, E, E, T, E, F, E, T, T, F, E, F, E, E, E]), ([E, E, T, E, E, F, E, T, E, F, T, E, F, E, E], [E, E, T, E, F, E, E, T, E, F, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1718 (And.intro z_1818 trivial))

theorem z_1820 : le (tf [E, F, E, E, T, E, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, E, T, T, F, E, E] [([E, F, E, E, E, T, E, E, F, E, T, T, F, E, E], [F, E, E, E, E, T, E, E, F, E, T, T, F, E, E]), ([E, F, E, E, T, E, E, E, F, E, T, E, F, T, E], [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_573 (And.intro z_1782 trivial))

theorem z_1821 : le (tf [F, E, E, E, T, E, E, E, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, F, T, E, E, F, E, T] [([F, E, E, E, E, T, E, E, F, T, E, E, F, E, T], [F, E, E, E, E, T, E, F, E, T, E, E, F, E, T]), ([F, E, E, E, T, E, E, E, F, E, T, E, F, E, T], [F, E, E, E, T, E, E, F, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_574 (And.intro z_1781 trivial))

theorem z_1822 : le (tf [E, F, E, E, T, E, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, F, T, E, E, F, T, E] [([E, F, E, E, E, T, E, E, F, T, E, E, F, T, E], [F, E, E, E, E, T, E, E, F, T, E, E, F, T, E]), ([E, F, E, E, T, E, E, E, F, E, T, E, F, T, E], [F, E, E, E, T, E, E, E, F, E, T, E, F, T, E]), ([E, F, E, E, T, E, E, E, F, T, E, E, F, E, T], [F, E, E, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_575 (And.intro z_1782 (And.intro z_1821 trivial)))

theorem z_1823 : le (tf [E, E, F, E, T, E, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, F, T, E, T, F, E, E] [([E, E, F, E, E, T, E, E, F, T, E, T, F, E, E], [E, F, E, E, E, T, E, E, F, T, E, T, F, E, E]), ([E, E, F, E, T, E, E, E, F, E, T, T, F, E, E], [E, F, E, E, T, E, E, E, F, E, T, T, F, E, E]), ([E, E, F, E, T, E, E, E, F, T, E, E, F, T, E], [E, F, E, E, T, E, E, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_576 (And.intro z_1820 (And.intro z_1822 trivial)))

theorem z_1824 : le (tf [F, E, T, E, E, E, E, F, E, E, T, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, F, E, E, T, E, F, E, T] [([F, E, E, T, E, E, E, F, E, E, T, E, F, E, T], [F, E, E, T, E, E, E, F, E, E, T, F, E, E, T]), ([F, E, T, E, E, E, E, F, E, E, E, T, F, E, T], [F, E, T, E, E, E, F, E, E, E, E, T, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_504 (And.intro z_1078 trivial))

theorem z_1825 : le (tf [F, E, T, E, E, E, E, E, F, E, T, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, E, T, E, F, T, E] [([F, E, E, T, E, E, E, E, F, E, T, E, F, T, E], [F, E, E, T, E, E, E, E, F, E, T, F, E, T, E]), ([F, E, T, E, E, E, E, E, F, E, E, T, F, T, E], [F, E, T, E, E, E, E, F, E, E, E, T, F, T, E]), ([F, E, T, E, E, E, E, E, F, E, T, E, F, E, T], [F, E, T, E, E, E, E, F, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_505 (And.intro z_1079 (And.intro z_1824 trivial)))

theorem z_1826 : le (tf [E, F, T, E, E, E, E, E, F, E, T, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, F, E, T, T, F, E, E] [([E, F, E, T, E, E, E, E, F, E, T, T, F, E, E], [F, E, E, T, E, E, E, E, F, E, T, T, F, E, E]), ([E, F, T, E, E, E, E, E, F, E, T, E, F, T, E], [F, E, T, E, E, E, E, E, F, E, T, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_591 (And.intro z_1825 trivial))

theorem z_1827 : le (tf [F, E, T, E, E, E, E, E, F, T, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, T, E, E, E, E, E, F, T, E, E, F, E, T] [([F, E, E, T, E, E, E, E, F, T, E, E, F, E, T], [F, E, E, T, E, E, E, F, E, T, E, E, F, E, T]), ([F, E, T, E, E, E, E, E, F, E, T, E, F, E, T], [F, E, T, E, E, E, E, F, E, E, T, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_592 (And.intro z_1824 trivial))

theorem z_1828 : le (tf [E, F, T, E, E, E, E, E, F, T, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, F, T, E, E, F, T, E] [([E, F, E, T, E, E, E, E, F, T, E, E, F, T, E], [F, E, E, T, E, E, E, E, F, T, E, E, F, T, E]), ([E, F, T, E, E, E, E, E, F, E, T, E, F, T, E], [F, E, T, E, E, E, E, E, F, E, T, E, F, T, E]), ([E, F, T, E, E, E, E, E, F, T, E, E, F, E, T], [F, E, T, E, E, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_593 (And.intro z_1825 (And.intro z_1827 trivial)))

theorem z_1829 : le (tf [E, E, T, F, E, E, E, E, F, T, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, F, T, E, T, F, E, E] [([E, E, E, F, T, E, E, E, F, T, E, T, F, E, E], [E, E, F, E, T, E, E, E, F, T, E, T, F, E, E]), ([E, E, T, F, E, E, E, E, F, E, T, T, F, E, E], [E, F, T, E, E, E, E, E, F, E, T, T, F, E, E]), ([E, E, T, F, E, E, E, E, F, T, E, E, F, T, E], [E, F, T, E, E, E, E, E, F, T, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1823 (And.intro z_1826 (And.intro z_1828 trivial)))

theorem z_1830 : le (tf [E, E, T, E, F, E, E, E, F, T, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, E, F, T, T, E, F, E, E] [([E, E, E, T, F, E, E, E, F, T, T, E, F, E, E], [E, E, F, T, E, E, E, E, F, T, T, E, F, E, E]), ([E, E, T, E, F, E, E, E, F, T, E, T, F, E, E], [E, E, T, F, E, E, E, E, F, T, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_595 (And.intro z_1829 trivial))

theorem z_1831 : le (tf [E, F, E, E, T, E, E, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, T, F, E, E, E, F, E, T] [([E, F, E, E, E, T, E, T, F, E, E, E, F, E, T], [F, E, E, E, E, T, E, T, F, E, E, E, F, E, T]), ([E, F, E, E, T, E, E, E, F, T, E, E, F, E, T], [F, E, E, E, T, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_578 (And.intro z_1821 trivial))

theorem z_1832 : le (tf [E, E, F, E, T, E, E, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, T, F, E, E, E, F, T, E] [([E, E, F, E, E, T, E, T, F, E, E, E, F, T, E], [E, F, E, E, E, T, E, T, F, E, E, E, F, T, E]), ([E, E, F, E, T, E, E, E, F, T, E, E, F, T, E], [E, F, E, E, T, E, E, E, F, T, E, E, F, T, E]), ([E, E, F, E, T, E, E, T, F, E, E, E, F, E, T], [E, F, E, E, T, E, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_579 (And.intro z_1822 (And.intro z_1831 trivial)))

theorem z_1833 : le (tf [E, F, T, E, E, E, E, T, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, T, F, E, E, E, F, E, T] [([E, F, E, T, E, E, E, T, F, E, E, E, F, E, T], [E, F, E, T, E, E, E, T, F, E, E, F, E, E, T]), ([E, F, T, E, E, E, E, E, F, T, E, E, F, E, T], [F, E, T, E, E, E, E, E, F, T, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1764 (And.intro z_1827 trivial))

theorem z_1834 : le (tf [E, E, T, F, E, E, E, T, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, T, F, E, E, E, F, T, E] [([E, E, E, F, T, E, E, T, F, E, E, E, F, T, E], [E, E, F, E, T, E, E, T, F, E, E, E, F, T, E]), ([E, E, T, F, E, E, E, E, F, T, E, E, F, T, E], [E, F, T, E, E, E, E, E, F, T, E, E, F, T, E]), ([E, E, T, F, E, E, E, T, F, E, E, E, F, E, T], [E, F, T, E, E, E, E, T, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1832 (And.intro z_1828 (And.intro z_1833 trivial)))

theorem z_1835 : le (tf [E, E, T, E, F, E, E, T, F, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, T, F, E, E, T, F, E, E] [([E, E, E, T, F, E, E, T, F, E, E, T, F, E, E], [E, E, E, T, F, E, E, T, F, E, F, T, E, E, E]), ([E, E, T, E, F, E, E, E, F, T, E, T, F, E, E], [E, E, T, F, E, E, E, E, F, T, E, T, F, E, E]), ([E, E, T, E, F, E, E, T, F, E, E, E, F, T, E], [E, E, T, F, E, E, E, T, F, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_727 (And.intro z_1829 (And.intro z_1834 trivial)))

theorem z_1836 : le (tf [E, E, T, E, E, F, E, T, F, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, F, E, T, F, E, T, E, F, E, E] [([E, E, E, T, E, F, E, T, F, E, T, E, F, E, E], [E, E, E, T, F, E, E, T, F, E, T, E, F, E, E]), ([E, E, T, E, E, F, E, E, F, T, T, E, F, E, E], [E, E, T, E, F, E, E, E, F, T, T, E, F, E, E]), ([E, E, T, E, E, F, E, T, F, E, E, T, F, E, E], [E, E, T, E, F, E, E, T, F, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_728 (And.intro z_1830 (And.intro z_1835 trivial)))

theorem z_1837 : le (tf [E, F, E, E, T, E, T, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, T, F, E, E, E, E, F, E, T] [([E, F, E, E, E, T, T, F, E, E, E, E, F, E, T], [F, E, E, E, E, T, T, F, E, E, E, E, F, E, T]), ([E, F, E, E, T, E, E, F, T, E, E, E, F, E, T], [F, E, E, E, T, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_747 (And.intro z_1784 trivial))

theorem z_1838 : le (tf [E, E, F, E, T, E, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, T, F, E, E, E, E, F, T, E] [([E, E, F, E, E, T, T, F, E, E, E, E, F, T, E], [E, F, E, E, E, T, T, F, E, E, E, E, F, T, E]), ([E, E, F, E, T, E, E, F, T, E, E, E, F, T, E], [E, F, E, E, T, E, E, F, T, E, E, E, F, T, E]), ([E, E, F, E, T, E, T, F, E, E, E, E, F, E, T], [E, F, E, E, T, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1327 (And.intro z_1789 (And.intro z_1837 trivial)))

theorem z_1839 : le (tf [E, F, T, E, E, E, T, F, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, T, F, E, E, E, E, F, E, T] [([E, F, E, T, E, E, T, F, E, E, E, E, F, E, T], [F, E, E, T, E, E, T, F, E, E, E, E, F, E, T]), ([E, F, T, E, E, E, E, F, T, E, E, E, F, E, T], [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1376 (And.intro z_1808 trivial))

theorem z_1840 : le (tf [E, E, T, F, E, E, T, F, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, T, F, E, E, E, E, F, T, E] [([E, E, E, F, T, E, T, F, E, E, E, E, F, T, E], [E, E, F, E, T, E, T, F, E, E, E, E, F, T, E]), ([E, E, T, F, E, E, E, F, T, E, E, E, F, T, E], [E, F, T, E, E, E, E, F, T, E, E, E, F, T, E]), ([E, E, T, F, E, E, T, F, E, E, E, E, F, E, T], [E, F, T, E, E, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1838 (And.intro z_1809 (And.intro z_1839 trivial)))

theorem z_1841 : le (tf [E, E, T, E, F, E, T, F, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, T, F, E, E, E, T, F, E, E] [([E, E, E, T, F, E, T, F, E, E, E, T, F, E, E], [E, E, E, T, F, E, T, F, E, E, F, T, E, E, E]), ([E, E, T, E, F, E, E, F, T, E, E, T, F, E, E], [E, E, T, F, E, E, E, F, T, E, E, T, F, E, E]), ([E, E, T, E, F, E, T, F, E, E, E, E, F, T, E], [E, E, T, F, E, E, T, F, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1362 (And.intro z_1810 (And.intro z_1840 trivial)))

theorem z_1842 : le (tf [E, F, E, E, T, T, E, E, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, E, F, E, E, E, F, E, T] [([E, F, E, E, T, E, T, E, F, E, E, E, F, E, T], [E, F, E, E, T, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1837 trivial)

theorem z_1843 : le (tf [E, E, F, E, T, T, E, E, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, E, F, E, E, E, F, T, E] [([E, E, F, E, T, E, T, E, F, E, E, E, F, T, E], [E, E, F, E, T, E, T, F, E, E, E, E, F, T, E]), ([E, E, F, E, T, T, E, E, F, E, E, E, F, E, T], [E, F, E, E, T, T, E, E, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1838 (And.intro z_1842 trivial))

theorem z_1844 : le (tf [E, F, T, E, E, T, E, E, F, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, E, F, E, E, E, F, E, T] [([E, F, E, T, E, T, E, E, F, E, E, E, F, E, T], [E, F, E, T, E, T, E, F, E, E, E, E, F, E, T]), ([E, F, T, E, E, E, T, E, F, E, E, E, F, E, T], [E, F, T, E, E, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1378 (And.intro z_1839 trivial))

theorem z_1845 : le (tf [E, E, T, F, E, T, E, E, F, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, E, F, E, E, E, F, T, E] [([E, E, E, F, T, T, E, E, F, E, E, E, F, T, E], [E, E, F, E, T, T, E, E, F, E, E, E, F, T, E]), ([E, E, T, F, E, E, T, E, F, E, E, E, F, T, E], [E, E, T, F, E, E, T, F, E, E, E, E, F, T, E]), ([E, E, T, F, E, T, E, E, F, E, E, E, F, E, T], [E, F, T, E, E, T, E, E, F, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1843 (And.intro z_1840 (And.intro z_1844 trivial)))

theorem z_1846 : le (tf [E, E, T, E, F, T, E, E, F, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, T, E, E, F, E, E, T, F, E, E] [([E, E, E, T, F, T, E, E, F, E, E, T, F, E, E], [E, E, E, T, F, T, E, F, E, E, E, T, F, E, E]), ([E, E, T, E, F, E, T, E, F, E, E, T, F, E, E], [E, E, T, E, F, E, T, F, E, E, E, T, F, E, E]), ([E, E, T, E, F, T, E, E, F, E, E, E, F, T, E], [E, E, T, F, E, T, E, E, F, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1380 (And.intro z_1841 (And.intro z_1845 trivial)))

theorem z_1847 : le (tf [E, E, T, E, E, T, F, E, F, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, F, E, F, E, T, E, F, E, E] [([E, E, E, T, E, T, F, E, F, E, T, E, F, E, E], [E, E, E, T, E, T, F, E, F, E, T, F, E, E, E]), ([E, E, T, E, E, E, F, T, F, E, T, E, F, E, E], [E, E, T, E, E, F, E, T, F, E, T, E, F, E, E]), ([E, E, T, E, E, T, F, E, F, E, E, T, F, E, E], [E, E, T, E, F, T, E, E, F, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1779 (And.intro z_1836 (And.intro z_1846 trivial)))

theorem z_1848 : le (tf [E, E, T, E, E, T, F, E, T, F, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, F, E, T, F, E, E, F, E, E] [([E, E, E, T, E, T, F, E, T, F, E, E, F, E, E], [E, E, E, T, E, T, F, E, T, F, E, F, E, E, E]), ([E, E, T, E, E, E, F, T, T, F, E, E, F, E, E], [E, E, T, E, E, F, E, T, T, F, E, E, F, E, E]), ([E, E, T, E, E, T, F, E, E, F, T, E, F, E, E], [E, E, T, E, E, T, F, E, F, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1780 (And.intro z_1819 (And.intro z_1847 trivial)))

theorem z_1849 : le (tf [E, F, E, T, E, E, E, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, T, F, E, T, E, F, E] [([E, F, E, E, T, E, E, E, T, F, E, T, E, F, E], [F, E, E, E, T, E, E, E, T, F, E, T, E, F, E]), ([E, F, E, T, E, E, E, E, E, F, T, T, E, F, E], [F, E, E, T, E, E, E, E, E, F, T, T, E, F, E]), ([E, F, E, T, E, E, E, E, T, F, E, E, T, F, E], [F, E, E, T, E, E, E, E, T, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_824 (And.intro z_507 (And.intro z_827 trivial)))

theorem z_1850 : le (tf [F, T, E, E, E, F, E, E, E, E, E, F, E, T, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, F, E, E, E, E, E, F, E, T, T] [([F, E, T, E, E, F, E, E, E, E, E, F, E, T, T], [F, E, T, E, F, E, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_829 trivial)

theorem z_1851 : le (tf [F, T, E, E, E, E, F, E, E, E, E, F, T, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, E, F, T, E, T] [([F, E, T, E, E, E, F, E, E, E, E, F, T, E, T], [F, E, T, E, E, F, E, E, E, E, E, F, T, E, T]), ([F, T, E, E, E, E, F, E, E, E, E, F, E, T, T], [F, T, E, E, E, F, E, E, E, E, E, F, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_830 (And.intro z_1850 trivial))

theorem z_1852 : le (tf [F, T, E, E, E, E, E, F, E, E, E, F, T, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, E, E, F, T, T, E] [([F, E, T, E, E, E, E, F, E, E, E, F, T, T, E], [F, E, T, E, E, E, F, E, E, E, E, F, T, T, E]), ([F, T, E, E, E, E, E, F, E, E, E, F, T, E, T], [F, T, E, E, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_831 (And.intro z_1851 trivial))

theorem z_1853 : le (tf [F, T, E, E, E, E, E, F, E, E, T, F, E, E, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, E, T, F, E, E, T] [([F, E, T, E, E, E, E, F, E, E, T, F, E, E, T], [F, E, T, E, E, E, F, E, E, E, T, F, E, E, T]), ([F, T, E, E, E, E, E, F, E, E, E, F, T, E, T], [F, T, E, E, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_832 (And.intro z_1851 trivial))

theorem z_1854 : le (tf [F, T, E, E, E, E, E, E, F, E, T, F, E, T, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, E, T, F, E, T, E] [([F, E, T, E, E, E, E, E, F, E, T, F, E, T, E], [F, E, T, E, E, E, E, F, E, E, T, F, E, T, E]), ([F, T, E, E, E, E, E, E, F, E, E, F, T, T, E], [F, T, E, E, E, E, E, F, E, E, E, F, T, T, E]), ([F, T, E, E, E, E, E, E, F, E, T, F, E, E, T], [F, T, E, E, E, E, E, F, E, E, T, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_833 (And.intro z_1852 (And.intro z_1853 trivial)))

theorem z_1855 : le (tf [F, T, E, E, E, E, E, E, E, F, T, F, T, E, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, E, F, T, F, T, E, E] [([F, E, T, E, E, E, E, E, E, F, T, F, T, E, E], [F, E, T, E, E, E, E, E, F, E, T, F, T, E, E]), ([F, T, E, E, E, E, E, E, E, F, T, F, E, T, E], [F, T, E, E, E, E, E, E, F, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_834 (And.intro z_1854 trivial))

theorem z_1856 : le (tf [F, T, E, E, E, E, E, E, E, F, T, T, E, F, E]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, E, F, T, T, E, F, E] [([F, E, T, E, E, E, E, E, E, F, T, T, E, F, E], [F, E, T, E, E, E, E, E, F, E, T, T, E, F, E]), ([F, T, E, E, E, E, E, E, E, F, T, E, T, F, E], [F, T, E, E, E, E, E, E, E, F, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_868 (And.intro z_1855 trivial))

theorem z_1857 : le (tf [F, T, E, E, E, E, E, F, T, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, T, E, E, E, E, F, T] [([F, E, T, E, E, E, E, F, T, E, E, E, E, F, T], [F, E, T, E, E, E, E, F, T, E, E, E, F, E, T]), ([F, T, E, E, E, E, E, F, E, T, E, E, E, F, T], [F, T, E, E, E, E, F, E, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1808 (And.intro z_1052 trivial))

theorem z_1858 : le (tf [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E] [([E, E, F, T, E, E, E, F, T, E, E, E, T, F, E], [E, E, F, T, E, E, E, F, T, E, E, F, T, E, E]), ([E, T, F, E, E, E, E, F, E, T, E, E, T, F, E], [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E]), ([E, T, F, E, E, E, E, F, T, E, E, E, E, F, T], [F, T, E, E, E, E, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1324 (And.intro z_1053 (And.intro z_1857 trivial)))

theorem z_1859 : le (tf [E, T, F, E, E, E, E, E, T, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, T, F, E, T, E, F, E] [([E, E, F, T, E, E, E, E, T, F, E, T, E, F, E], [E, F, E, T, E, E, E, E, T, F, E, T, E, F, E]), ([E, T, F, E, E, E, E, E, E, F, T, T, E, F, E], [F, T, E, E, E, E, E, E, E, F, T, T, E, F, E]), ([E, T, F, E, E, E, E, E, T, F, E, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1849 (And.intro z_1856 (And.intro z_1858 trivial)))

theorem z_1860 : le (tf [E, T, E, F, E, E, E, E, T, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, E, T, F, T, E, E, F, E] [([E, E, T, F, E, E, E, E, T, F, T, E, E, F, E], [E, E, T, F, E, E, E, E, T, F, T, E, F, E, E]), ([E, T, E, F, E, E, E, E, T, F, E, T, E, F, E], [E, T, F, E, E, E, E, E, T, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1811 (And.intro z_1859 trivial))

theorem z_1861 : le (tf [F, T, E, E, E, E, E, T, E, F, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, T, E, F, E, E, E, F, T] [([F, E, T, E, E, E, E, T, E, F, E, E, E, F, T], [F, E, T, E, E, E, E, T, E, F, E, E, F, E, T]), ([F, T, E, E, E, E, E, E, T, F, E, E, E, F, T], [F, T, E, E, E, E, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1815 (And.intro z_1857 trivial))

theorem z_1862 : le (tf [E, T, F, E, E, E, E, T, E, F, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, E, F, E, E, T, F, E] [([E, E, F, T, E, E, E, T, E, F, E, E, T, F, E], [E, E, F, T, E, E, E, T, E, F, E, F, T, E, E]), ([E, T, F, E, E, E, E, E, T, F, E, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E]), ([E, T, F, E, E, E, E, T, E, F, E, E, E, F, T], [F, T, E, E, E, E, E, T, E, F, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1716 (And.intro z_1858 (And.intro z_1861 trivial)))

theorem z_1863 : le (tf [E, T, E, F, E, E, E, T, E, F, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, E, F, E, T, E, F, E] [([E, E, T, F, E, E, E, T, E, F, E, T, E, F, E], [E, E, T, F, E, E, E, T, E, F, E, T, F, E, E]), ([E, T, E, F, E, E, E, E, T, F, E, T, E, F, E], [E, T, F, E, E, E, E, E, T, F, E, T, E, F, E]), ([E, T, E, F, E, E, E, T, E, F, E, E, T, F, E], [E, T, F, E, E, E, E, T, E, F, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1817 (And.intro z_1859 (And.intro z_1862 trivial)))

theorem z_1864 : le (tf [E, T, E, E, F, E, E, T, E, F, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, T, E, F, T, E, E, F, E] [([E, E, T, E, F, E, E, T, E, F, T, E, E, F, E], [E, E, T, E, F, E, E, T, E, F, T, E, F, E, E]), ([E, T, E, E, F, E, E, E, T, F, T, E, E, F, E], [E, T, E, F, E, E, E, E, T, F, T, E, E, F, E]), ([E, T, E, E, F, E, E, T, E, F, E, T, E, F, E], [E, T, E, F, E, E, E, T, E, F, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1818 (And.intro z_1860 (And.intro z_1863 trivial)))

theorem z_1865 : le (tf [E, T, E, E, E, F, E, T, T, F, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, E, T, T, F, E, E, E, F, E] [([E, E, T, E, E, F, E, T, T, F, E, E, E, F, E], [E, E, T, E, E, F, E, T, T, F, E, E, F, E, E]), ([E, T, E, E, E, F, E, T, E, F, T, E, E, F, E], [E, T, E, E, F, E, E, T, E, F, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1819 (And.intro z_1864 trivial))

theorem z_1866 : le (tf [E, F, E, T, E, E, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, F, E, T, T, E, F, E] [([E, F, E, E, T, E, E, E, F, E, T, T, E, F, E], [F, E, E, E, T, E, E, E, F, E, T, T, E, F, E]), ([E, F, E, T, E, E, E, E, F, E, T, E, T, F, E], [E, F, E, T, E, E, E, E, F, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_500 (And.intro z_1754 trivial))

theorem z_1867 : le (tf [E, F, E, E, T, F, E, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, F, E, E, E, E, E, T, T, F, E] [([E, F, E, E, E, F, T, E, E, E, E, T, T, F, E], [F, E, E, E, E, F, T, E, E, E, E, T, T, F, E]), ([E, F, E, E, T, F, E, E, E, E, E, T, E, F, T], [F, E, E, E, T, F, E, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_492 trivial))

theorem z_1868 : le (tf [E, F, E, E, T, E, F, E, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, E, E, E, T, E, T, F, E] [([E, F, E, E, E, T, F, E, E, E, T, E, T, F, E], [E, F, E, E, E, T, F, E, E, E, T, F, T, E, E]), ([E, F, E, E, T, E, F, E, E, E, E, T, T, F, E], [E, F, E, E, T, F, E, E, E, E, E, T, T, F, E]), ([E, F, E, E, T, E, F, E, E, E, T, E, E, F, T], [F, E, E, E, T, E, F, E, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_940 (And.intro z_1867 (And.intro z_493 trivial)))

theorem z_1869 : le (tf [E, F, E, T, E, E, F, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, F, E, E, E, E, T, T, F, E] [([E, F, E, E, T, E, F, E, E, E, E, T, T, F, E], [E, F, E, E, T, F, E, E, E, E, E, T, T, F, E]), ([E, F, E, T, E, E, F, E, E, E, E, T, E, F, T], [F, E, E, T, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1867 (And.intro z_840 trivial))

theorem z_1870 : le (tf [E, F, E, T, E, E, E, F, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, E, T, E, T, F, E] [([E, F, E, E, T, E, E, F, E, E, T, E, T, F, E], [E, F, E, E, T, E, F, E, E, E, T, E, T, F, E]), ([E, F, E, T, E, E, E, F, E, E, E, T, T, F, E], [E, F, E, T, E, E, F, E, E, E, E, T, T, F, E]), ([E, F, E, T, E, E, E, F, E, E, T, E, E, F, T], [F, E, E, T, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1868 (And.intro z_1869 (And.intro z_841 trivial)))

theorem z_1871 : le (tf [F, T, E, E, E, E, F, E, E, E, E, T, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, F, E, E, E, E, T, E, F, T] [([F, E, T, E, E, E, F, E, E, E, E, T, E, F, T], [F, E, T, E, E, F, E, E, E, E, E, T, E, F, T]), ([F, T, E, E, E, E, F, E, E, E, E, E, T, F, T], [F, T, E, E, E, E, F, E, E, E, E, F, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_835 (And.intro z_1851 trivial))

theorem z_1872 : le (tf [E, T, F, E, E, E, F, E, E, E, E, T, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, F, E, E, E, E, T, T, F, E] [([E, E, F, T, E, E, F, E, E, E, E, T, T, F, E], [E, F, E, T, E, E, F, E, E, E, E, T, T, F, E]), ([E, T, F, E, E, E, F, E, E, E, E, T, E, F, T], [F, T, E, E, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1869 (And.intro z_1871 trivial))

theorem z_1873 : le (tf [F, T, E, E, E, E, E, F, E, E, T, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, F, E, E, T, E, E, F, T] [([F, E, T, E, E, E, E, F, E, E, T, E, E, F, T], [F, E, T, E, E, E, F, E, E, E, T, E, E, F, T]), ([F, T, E, E, E, E, E, F, E, E, E, T, E, F, T], [F, T, E, E, E, E, F, E, E, E, E, T, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_836 (And.intro z_1871 trivial))

theorem z_1874 : le (tf [E, T, F, E, E, E, E, F, E, E, T, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, E, E, T, E, T, F, E] [([E, E, F, T, E, E, E, F, E, E, T, E, T, F, E], [E, F, E, T, E, E, E, F, E, E, T, E, T, F, E]), ([E, T, F, E, E, E, E, F, E, E, E, T, T, F, E], [E, T, F, E, E, E, F, E, E, E, E, T, T, F, E]), ([E, T, F, E, E, E, E, F, E, E, T, E, E, F, T], [F, T, E, E, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1870 (And.intro z_1872 (And.intro z_1873 trivial)))

theorem z_1875 : le (tf [E, T, F, E, E, E, E, E, F, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, F, E, T, T, E, F, E] [([E, E, F, T, E, E, E, E, F, E, T, T, E, F, E], [E, F, E, T, E, E, E, E, F, E, T, T, E, F, E]), ([E, T, F, E, E, E, E, E, F, E, T, E, T, F, E], [E, T, F, E, E, E, E, F, E, E, T, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1866 (And.intro z_1874 trivial))

theorem z_1876 : le (tf [F, T, E, E, E, E, E, E, F, T, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, T, E, E, E, E, E, E, F, T, E, E, E, F, T] [([F, E, T, E, E, E, E, E, F, T, E, E, E, F, T], [F, E, T, E, E, E, E, F, E, T, E, E, E, F, T]), ([F, T, E, E, E, E, E, E, F, E, T, E, E, F, T], [F, T, E, E, E, E, E, F, E, E, T, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_837 (And.intro z_1873 trivial))

theorem z_1877 : le (tf [E, T, F, E, E, E, E, E, F, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, F, T, E, E, T, F, E] [([E, E, F, T, E, E, E, E, F, T, E, E, T, F, E], [E, E, F, T, E, E, E, E, F, T, E, F, T, E, E]), ([E, T, F, E, E, E, E, E, F, E, T, E, T, F, E], [E, T, F, E, E, E, E, F, E, E, T, E, T, F, E]), ([E, T, F, E, E, E, E, E, F, T, E, E, E, F, T], [F, T, E, E, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1757 (And.intro z_1874 (And.intro z_1876 trivial)))

theorem z_1878 : le (tf [E, T, E, F, E, E, E, E, F, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, E, F, T, E, T, E, F, E] [([E, E, T, F, E, E, E, E, F, T, E, T, E, F, E], [E, E, T, F, E, E, E, E, F, T, E, T, F, E, E]), ([E, T, E, F, E, E, E, E, F, E, T, T, E, F, E], [E, T, F, E, E, E, E, E, F, E, T, T, E, F, E]), ([E, T, E, F, E, E, E, E, F, T, E, E, T, F, E], [E, T, F, E, E, E, E, E, F, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1829 (And.intro z_1875 (And.intro z_1877 trivial)))

theorem z_1879 : le (tf [E, T, E, E, F, E, E, E, F, T, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, E, F, T, T, E, E, F, E] [([E, E, T, E, F, E, E, E, F, T, T, E, E, F, E], [E, E, T, E, F, E, E, E, F, T, T, E, F, E, E]), ([E, T, E, E, F, E, E, E, F, T, E, T, E, F, E], [E, T, E, F, E, E, E, E, F, T, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1830 (And.intro z_1878 trivial))

theorem z_1880 : le (tf [E, F, E, E, E, T, F, T, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, F, T, E, E, E, E, T, F, E] [([E, F, E, E, E, T, F, E, T, E, E, E, T, F, E], [F, E, E, E, E, T, F, E, T, E, E, E, T, F, E]), ([E, F, E, E, E, T, F, T, E, E, E, E, E, F, T], [F, E, E, E, E, T, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_419 (And.intro z_556 trivial))

theorem z_1881 : le (tf [E, F, E, E, T, E, F, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, F, T, E, E, E, E, E, F, T] [([E, F, E, E, E, T, F, T, E, E, E, E, E, F, T], [F, E, E, E, E, T, F, T, E, E, E, E, E, F, T]), ([E, F, E, E, T, E, F, E, T, E, E, E, E, F, T], [F, E, E, E, T, E, F, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_556 (And.intro z_822 trivial))

theorem z_1882 : le (tf [E, E, F, E, T, E, F, T, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, F, T, E, E, E, E, T, F, E] [([E, E, F, E, E, T, F, T, E, E, E, E, T, F, E], [E, F, E, E, E, T, F, T, E, E, E, E, T, F, E]), ([E, E, F, E, T, E, F, E, T, E, E, E, T, F, E], [E, F, E, E, T, E, F, E, T, E, E, E, T, F, E]), ([E, E, F, E, T, E, F, T, E, E, E, E, E, F, T], [E, F, E, E, T, E, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1880 (And.intro z_1164 (And.intro z_1881 trivial)))

theorem z_1883 : le (tf [E, F, T, E, E, E, F, T, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, F, T, E, E, E, E, E, F, T] [([E, F, E, T, E, E, F, T, E, E, E, E, E, F, T], [F, E, E, T, E, E, F, T, E, E, E, E, E, F, T]), ([E, F, T, E, E, E, F, E, T, E, E, E, E, F, T], [E, F, T, E, E, F, E, E, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1459 (And.intro z_1173 trivial))

theorem z_1884 : le (tf [E, E, T, F, E, E, F, T, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, F, T, E, E, E, E, T, F, E] [([E, E, E, F, T, E, F, T, E, E, E, E, T, F, E], [E, E, F, E, T, E, F, T, E, E, E, E, T, F, E]), ([E, E, T, F, E, E, F, E, T, E, E, E, T, F, E], [E, E, T, F, E, F, E, E, T, E, E, E, T, F, E]), ([E, E, T, F, E, E, F, T, E, E, E, E, E, F, T], [E, F, T, E, E, E, F, T, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1882 (And.intro z_1174 (And.intro z_1883 trivial)))

theorem z_1885 : le (tf [E, F, E, T, E, E, E, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, T, F, E, E, E, E, F, T] [([E, F, E, E, T, E, E, T, F, E, E, E, E, F, T], [E, F, E, E, T, E, F, T, E, E, E, E, E, F, T]), ([E, F, E, T, E, E, E, E, F, T, E, E, E, F, T], [F, E, E, T, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1881 (And.intro z_1024 trivial))

theorem z_1886 : le (tf [E, T, F, E, E, E, E, T, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, T, F, E, E, E, E, F, T] [([E, E, F, T, E, E, E, T, F, E, E, E, E, F, T], [E, F, E, T, E, E, E, T, F, E, E, E, E, F, T]), ([E, T, F, E, E, E, E, E, F, T, E, E, E, F, T], [F, T, E, E, E, E, E, E, F, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1885 (And.intro z_1876 trivial))

theorem z_1887 : le (tf [E, T, E, F, E, E, E, T, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, T, F, E, E, E, T, F, E] [([E, E, T, F, E, E, E, T, F, E, E, E, T, F, E], [E, E, T, F, E, E, F, T, E, E, E, E, T, F, E]), ([E, T, E, F, E, E, E, E, F, T, E, E, T, F, E], [E, T, F, E, E, E, E, E, F, T, E, E, T, F, E]), ([E, T, E, F, E, E, E, T, F, E, E, E, E, F, T], [E, T, F, E, E, E, E, T, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1884 (And.intro z_1877 (And.intro z_1886 trivial)))

theorem z_1888 : le (tf [E, T, E, E, F, E, E, T, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, T, F, E, E, T, E, F, E] [([E, E, T, E, F, E, E, T, F, E, E, T, E, F, E], [E, E, T, E, F, E, E, T, F, E, E, T, F, E, E]), ([E, T, E, E, F, E, E, E, F, T, E, T, E, F, E], [E, T, E, F, E, E, E, E, F, T, E, T, E, F, E]), ([E, T, E, E, F, E, E, T, F, E, E, E, T, F, E], [E, T, E, F, E, E, E, T, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1835 (And.intro z_1878 (And.intro z_1887 trivial)))

theorem z_1889 : le (tf [E, T, E, E, E, F, E, T, F, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, E, T, F, E, T, E, E, F, E] [([E, E, T, E, E, F, E, T, F, E, T, E, E, F, E], [E, E, T, E, E, F, E, T, F, E, T, E, F, E, E]), ([E, T, E, E, E, F, E, E, F, T, T, E, E, F, E], [E, T, E, E, F, E, E, E, F, T, T, E, E, F, E]), ([E, T, E, E, E, F, E, T, F, E, E, T, E, F, E], [E, T, E, E, F, E, E, T, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1836 (And.intro z_1879 (And.intro z_1888 trivial)))

theorem z_1890 : le (tf [E, F, E, T, E, E, E, F, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, F, E, T, E, T, E, F, E] [([E, F, E, E, T, E, E, F, E, T, E, T, E, F, E], [F, E, E, E, T, E, E, F, E, T, E, T, E, F, E]), ([E, F, E, T, E, E, E, F, E, E, T, T, E, F, E], [F, E, E, T, E, E, E, F, E, E, T, T, E, F, E]), ([E, F, E, T, E, E, E, F, E, T, E, E, T, F, E], [F, E, E, T, E, E, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1156 (And.intro z_740 (And.intro z_517 trivial)))

theorem z_1891 : le (tf [E, T, F, E, E, E, E, F, E, T, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, F, E, T, E, T, E, F, E] [([E, E, F, T, E, E, E, F, E, T, E, T, E, F, E], [E, F, E, T, E, E, E, F, E, T, E, T, E, F, E]), ([E, T, F, E, E, E, E, F, E, E, T, T, E, F, E], [E, T, F, E, E, E, F, E, E, E, T, T, E, F, E]), ([E, T, F, E, E, E, E, F, E, T, E, E, T, F, E], [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1890 (And.intro z_1048 (And.intro z_1053 trivial)))

theorem z_1892 : le (tf [E, T, E, F, E, E, E, F, T, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, F, T, E, E, T, E, F, E] [([E, E, T, F, E, E, E, F, T, E, E, T, E, F, E], [E, E, T, F, E, E, F, E, T, E, E, T, E, F, E]), ([E, T, E, F, E, E, E, F, E, T, E, T, E, F, E], [E, T, F, E, E, E, E, F, E, T, E, T, E, F, E]), ([E, T, E, F, E, E, E, F, T, E, E, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1175 (And.intro z_1891 (And.intro z_1858 trivial)))

theorem z_1893 : le (tf [E, F, E, T, E, E, T, F, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, F, E, E, E, E, E, F, T] [([E, F, E, E, T, E, T, F, E, E, E, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, E, E, F, T]), ([E, F, E, T, E, E, E, F, T, E, E, E, E, F, T], [F, E, E, T, E, E, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1158 (And.intro z_826 trivial))

theorem z_1894 : le (tf [E, T, F, E, E, E, T, F, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, F, E, E, E, E, E, F, T] [([E, E, F, T, E, E, T, F, E, E, E, E, E, F, T], [E, F, E, T, E, E, T, F, E, E, E, E, E, F, T]), ([E, T, F, E, E, E, E, F, T, E, E, E, E, F, T], [F, T, E, E, E, E, E, F, T, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1893 (And.intro z_1857 trivial))

theorem z_1895 : le (tf [E, T, E, F, E, E, T, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, F, E, E, E, E, T, F, E] [([E, E, T, F, E, E, T, F, E, E, E, E, T, F, E], [E, E, T, F, E, E, T, F, E, E, E, F, T, E, E]), ([E, T, E, F, E, E, E, F, T, E, E, E, T, F, E], [E, T, F, E, E, E, E, F, T, E, E, E, T, F, E]), ([E, T, E, F, E, E, T, F, E, E, E, E, E, F, T], [E, T, F, E, E, E, T, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1217 (And.intro z_1858 (And.intro z_1894 trivial)))

theorem z_1896 : le (tf [E, T, E, E, F, E, T, F, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, F, E, E, E, T, E, F, E] [([E, E, T, E, F, E, T, F, E, E, E, T, E, F, E], [E, E, T, F, E, E, T, F, E, E, E, T, E, F, E]), ([E, T, E, E, F, E, E, F, T, E, E, T, E, F, E], [E, T, E, F, E, E, E, F, T, E, E, T, E, F, E]), ([E, T, E, E, F, E, T, F, E, E, E, E, T, F, E], [E, T, E, F, E, E, T, F, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1218 (And.intro z_1892 (And.intro z_1895 trivial)))

theorem z_1897 : le (tf [E, F, E, E, T, T, E, F, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, T, E, F, E, E, E, E, E, F, T] [([E, F, E, E, T, E, T, F, E, E, E, E, E, F, T], [F, E, E, E, T, E, T, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1158 trivial)

theorem z_1898 : le (tf [E, E, F, E, T, T, E, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, T, E, F, E, E, E, E, T, F, E] [([E, E, F, E, T, E, T, F, E, E, E, E, T, F, E], [E, F, E, E, T, E, T, F, E, E, E, E, T, F, E]), ([E, E, F, E, T, T, E, F, E, E, E, E, E, F, T], [E, F, E, E, T, T, E, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1159 (And.intro z_1897 trivial))

theorem z_1899 : le (tf [E, F, T, E, E, T, E, F, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, T, E, F, E, E, E, E, E, F, T] [([E, F, E, T, E, T, E, F, E, E, E, E, E, F, T], [E, F, E, T, E, T, F, E, E, E, E, E, E, F, T]), ([E, F, T, E, E, E, T, F, E, E, E, E, E, F, T], [E, F, T, E, E, E, T, F, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1460 (And.intro z_1839 trivial))

theorem z_1900 : le (tf [E, E, T, F, E, T, E, F, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, T, E, F, E, E, E, E, T, F, E] [([E, E, E, F, T, T, E, F, E, E, E, E, T, F, E], [E, E, F, E, T, T, E, F, E, E, E, E, T, F, E]), ([E, E, T, F, E, E, T, F, E, E, E, E, T, F, E], [E, E, T, F, E, E, T, F, E, E, E, F, T, E, E]), ([E, E, T, F, E, T, E, F, E, E, E, E, E, F, T], [E, F, T, E, E, T, E, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1898 (And.intro z_1217 (And.intro z_1899 trivial)))

theorem z_1901 : le (tf [E, F, E, T, E, T, E, E, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, F, E, E, E, E, F, T] [([E, F, E, E, T, T, E, E, F, E, E, E, E, F, T], [E, F, E, E, T, T, E, F, E, E, E, E, E, F, T]), ([E, F, E, T, E, E, T, E, F, E, E, E, E, F, T], [E, F, E, T, E, E, T, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1897 (And.intro z_1893 trivial))

theorem z_1902 : le (tf [E, T, F, E, E, T, E, E, F, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, F, E, E, E, E, F, T] [([E, E, F, T, E, T, E, E, F, E, E, E, E, F, T], [E, F, E, T, E, T, E, E, F, E, E, E, E, F, T]), ([E, T, F, E, E, E, T, E, F, E, E, E, E, F, T], [E, T, F, E, E, E, T, F, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1901 (And.intro z_1894 trivial))

theorem z_1903 : le (tf [E, T, E, F, E, T, E, E, F, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, F, E, E, E, T, F, E] [([E, E, T, F, E, T, E, E, F, E, E, E, T, F, E], [E, E, T, F, E, T, E, F, E, E, E, E, T, F, E]), ([E, T, E, F, E, E, T, E, F, E, E, E, T, F, E], [E, T, E, F, E, E, T, F, E, E, E, E, T, F, E]), ([E, T, E, F, E, T, E, E, F, E, E, E, E, F, T], [E, T, F, E, E, T, E, E, F, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1900 (And.intro z_1895 (And.intro z_1902 trivial)))

theorem z_1904 : le (tf [E, T, E, E, F, T, E, E, F, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, T, E, E, F, E, E, T, E, F, E] [([E, E, T, E, F, T, E, E, F, E, E, T, E, F, E], [E, E, T, E, F, T, E, E, F, E, E, T, F, E, E]), ([E, T, E, E, F, E, T, E, F, E, E, T, E, F, E], [E, T, E, E, F, E, T, F, E, E, E, T, E, F, E]), ([E, T, E, E, F, T, E, E, F, E, E, E, T, F, E], [E, T, E, F, E, T, E, E, F, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1846 (And.intro z_1896 (And.intro z_1903 trivial)))

theorem z_1905 : le (tf [E, T, E, E, E, T, F, E, F, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, F, E, F, E, T, E, E, F, E] [([E, E, T, E, E, T, F, E, F, E, T, E, E, F, E], [E, E, T, E, E, T, F, E, F, E, T, E, F, E, E]), ([E, T, E, E, E, E, F, T, F, E, T, E, E, F, E], [E, T, E, E, E, F, E, T, F, E, T, E, E, F, E]), ([E, T, E, E, E, T, F, E, F, E, E, T, E, F, E], [E, T, E, E, F, T, E, E, F, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1847 (And.intro z_1889 (And.intro z_1904 trivial)))

theorem z_1906 : le (tf [E, T, E, E, E, T, F, E, T, F, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, F, E, T, F, E, E, E, F, E] [([E, E, T, E, E, T, F, E, T, F, E, E, E, F, E], [E, E, T, E, E, T, F, E, T, F, E, E, F, E, E]), ([E, T, E, E, E, E, F, T, T, F, E, E, E, F, E], [E, T, E, E, E, F, E, T, T, F, E, E, E, F, E]), ([E, T, E, E, E, T, F, E, E, F, T, E, E, F, E], [E, T, E, E, E, T, F, E, F, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1848 (And.intro z_1865 (And.intro z_1905 trivial)))

theorem z_1907 : le (tf [E, T, E, E, E, T, F, T, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, F, T, E, F, E, E, E, E, F] [([E, E, T, E, E, T, F, T, E, F, E, E, E, E, F], [E, E, T, E, E, T, F, T, F, E, E, E, E, E, F]), ([E, T, E, E, E, T, F, E, T, F, E, E, E, E, F], [E, T, E, E, E, T, F, E, T, F, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1696 (And.intro z_1906 trivial))

theorem z_1908 : le (tf [E, T, E, E, T, E, F, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, E, F, T, E, E, F, E, E, E, F] [([E, E, T, E, T, E, F, T, E, E, F, E, E, E, F], [E, E, T, E, T, F, E, T, E, E, F, E, E, E, F]), ([E, T, E, E, E, T, F, T, E, E, F, E, E, E, F], [E, T, E, E, E, T, F, T, E, F, E, E, E, E, F]), ([E, T, E, E, T, E, F, E, T, E, F, E, E, E, F], [E, T, E, E, T, F, E, E, T, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1408 (And.intro z_1907 (And.intro z_1474 trivial)))

theorem z_1909 : le (tf [T, E, F, E, E, E, E, T, E, F, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, E, F, E, E, T, E, F] [([E, T, F, E, E, E, E, T, E, F, E, E, T, E, F], [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F]), ([T, E, F, E, E, E, E, E, T, F, E, E, T, E, F], [T, F, E, E, E, E, E, E, T, F, E, E, T, E, F]), ([T, E, F, E, E, E, E, T, E, F, E, E, E, T, F], [T, F, E, E, E, E, E, T, E, F, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1122 (And.intro z_1576 (And.intro z_1610 trivial)))

theorem z_1910 : le (tf [T, E, E, F, E, E, E, T, E, F, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, T, E, F, E, T, E, E, F] [([E, T, E, F, E, E, E, T, E, F, E, T, E, E, F], [E, T, F, E, E, E, E, T, E, F, E, T, E, E, F]), ([T, E, E, F, E, E, E, E, T, F, E, T, E, E, F], [T, E, F, E, E, E, E, E, T, F, E, T, E, E, F]), ([T, E, E, F, E, E, E, T, E, F, E, E, T, E, F], [T, E, F, E, E, E, E, T, E, F, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1123 (And.intro z_1577 (And.intro z_1909 trivial)))

theorem z_1911 : le (tf [T, E, E, E, F, E, E, T, E, F, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, T, E, F, T, E, E, E, F] [([E, T, E, E, F, E, E, T, E, F, T, E, E, E, F], [E, T, E, F, E, E, E, T, E, F, T, E, E, E, F]), ([T, E, E, E, F, E, E, E, T, F, T, E, E, E, F], [T, E, E, F, E, E, E, E, T, F, T, E, E, E, F]), ([T, E, E, E, F, E, E, T, E, F, E, T, E, E, F], [T, E, E, F, E, E, E, T, E, F, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1246 (And.intro z_1578 (And.intro z_1910 trivial)))

theorem z_1912 : le (tf [T, E, E, E, E, F, E, T, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, F, E, T, T, F, E, E, E, E, F] [([E, T, E, E, E, F, E, T, T, F, E, E, E, E, F], [E, T, E, E, F, E, E, T, T, F, E, E, E, E, F]), ([T, E, E, E, E, F, E, T, E, F, T, E, E, E, F], [T, E, E, E, F, E, E, T, E, F, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1410 (And.intro z_1911 trivial))

theorem z_1913 : le (tf [T, E, F, E, E, E, E, E, F, E, T, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, E, F, E, T, T, E, E, F] [([E, T, F, E, E, E, E, E, F, E, T, T, E, E, F], [E, T, F, E, E, E, E, F, E, E, T, T, E, E, F]), ([T, E, F, E, E, E, E, E, F, E, T, E, T, E, F], [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1546 (And.intro z_1567 trivial))

theorem z_1914 : le (tf [T, E, F, E, E, E, E, E, F, T, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, E, F, T, E, E, T, E, F] [([E, T, F, E, E, E, E, E, F, T, E, E, T, E, F], [E, T, F, E, E, E, E, F, E, T, E, E, T, E, F]), ([T, E, F, E, E, E, E, E, F, E, T, E, T, E, F], [T, F, E, E, E, E, E, E, F, E, T, E, T, E, F]), ([T, E, F, E, E, E, E, E, F, T, E, E, E, T, F], [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1119 (And.intro z_1567 (And.intro z_1592 trivial)))

theorem z_1915 : le (tf [T, E, E, F, E, E, E, E, F, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, E, F, T, E, T, E, E, F] [([E, T, E, F, E, E, E, E, F, T, E, T, E, E, F], [E, T, F, E, E, E, E, E, F, T, E, T, E, E, F]), ([T, E, E, F, E, E, E, E, F, E, T, T, E, E, F], [T, E, F, E, E, E, E, E, F, E, T, T, E, E, F]), ([T, E, E, F, E, E, E, E, F, T, E, E, T, E, F], [T, E, F, E, E, E, E, E, F, T, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1547 (And.intro z_1913 (And.intro z_1914 trivial)))

theorem z_1916 : le (tf [T, E, E, E, F, E, E, E, F, T, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, E, F, T, T, E, E, E, F] [([E, T, E, E, F, E, E, E, F, T, T, E, E, E, F], [E, T, E, F, E, E, E, E, F, T, T, E, E, E, F]), ([T, E, E, E, F, E, E, E, F, T, E, T, E, E, F], [T, E, E, F, E, E, E, E, F, T, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1554 (And.intro z_1915 trivial))

theorem z_1917 : le (tf [T, E, F, E, E, E, E, T, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, T, F, E, E, E, E, T, F] [([E, T, F, E, E, E, E, T, F, E, E, E, E, T, F], [E, T, F, E, E, E, F, T, E, E, E, E, E, T, F]), ([T, E, F, E, E, E, E, E, F, T, E, E, E, T, F], [T, F, E, E, E, E, E, E, F, T, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1121 (And.intro z_1592 trivial))

theorem z_1918 : le (tf [T, E, E, F, E, E, E, T, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, T, F, E, E, E, T, E, F] [([E, T, E, F, E, E, E, T, F, E, E, E, T, E, F], [E, T, F, E, E, E, E, T, F, E, E, E, T, E, F]), ([T, E, E, F, E, E, E, E, F, T, E, E, T, E, F], [T, E, F, E, E, E, E, E, F, T, E, E, T, E, F]), ([T, E, E, F, E, E, E, T, F, E, E, E, E, T, F], [T, E, F, E, E, E, E, T, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1122 (And.intro z_1914 (And.intro z_1917 trivial)))

theorem z_1919 : le (tf [T, E, E, E, F, E, E, T, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, T, F, E, E, T, E, E, F] [([E, T, E, E, F, E, E, T, F, E, E, T, E, E, F], [E, T, E, F, E, E, E, T, F, E, E, T, E, E, F]), ([T, E, E, E, F, E, E, E, F, T, E, T, E, E, F], [T, E, E, F, E, E, E, E, F, T, E, T, E, E, F]), ([T, E, E, E, F, E, E, T, F, E, E, E, T, E, F], [T, E, E, F, E, E, E, T, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1555 (And.intro z_1915 (And.intro z_1918 trivial)))

theorem z_1920 : le (tf [T, E, E, E, E, F, E, T, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, F, E, T, F, E, T, E, E, E, F] [([E, T, E, E, E, F, E, T, F, E, T, E, E, E, F], [E, T, E, E, F, E, E, T, F, E, T, E, E, E, F]), ([T, E, E, E, E, F, E, E, F, T, T, E, E, E, F], [T, E, E, E, F, E, E, E, F, T, T, E, E, E, F]), ([T, E, E, E, E, F, E, T, F, E, E, T, E, E, F], [T, E, E, E, F, E, E, T, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1556 (And.intro z_1916 (And.intro z_1919 trivial)))

theorem z_1921 : le (tf [T, E, F, E, E, E, E, F, E, E, T, F, T, E, E]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, E, E, T, F, T, E, E] [([E, T, F, E, E, E, E, F, E, E, T, F, T, E, E], [E, T, F, E, E, E, F, E, E, E, T, F, T, E, E]), ([T, E, F, E, E, E, E, F, E, E, T, F, E, T, E], [T, F, E, E, E, E, E, F, E, E, T, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1047 (And.intro z_1642 trivial))

theorem z_1922 : le (tf [T, E, F, E, E, E, E, F, E, E, T, T, E, F, E]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, E, E, T, T, E, F, E] [([E, T, F, E, E, E, E, F, E, E, T, T, E, F, E], [E, T, F, E, E, E, F, E, E, E, T, T, E, F, E]), ([T, E, F, E, E, E, E, F, E, E, T, E, T, F, E], [T, E, F, E, E, E, E, F, E, E, T, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1048 (And.intro z_1921 trivial))

theorem z_1923 : le (tf [T, E, F, E, E, E, E, F, E, T, E, E, T, F, E]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, E, T, E, E, T, F, E] [([E, T, F, E, E, E, E, F, E, T, E, E, T, F, E], [E, T, F, E, E, E, F, E, E, T, E, E, T, F, E]), ([T, E, F, E, E, E, E, F, E, E, T, E, T, F, E], [T, E, F, E, E, E, E, F, E, E, T, F, T, E, E]), ([T, E, F, E, E, E, E, F, E, T, E, E, E, F, T], [T, F, E, E, E, E, E, F, E, T, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1053 (And.intro z_1921 (And.intro z_1646 trivial)))

theorem z_1924 : le (tf [T, E, F, E, E, E, E, F, E, T, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, E, T, E, T, E, E, F] [([E, T, F, E, E, E, E, F, E, T, E, T, E, E, F], [E, T, F, E, E, E, F, E, E, T, E, T, E, E, F]), ([T, E, F, E, E, E, E, F, E, E, T, T, E, E, F], [T, E, F, E, E, E, E, F, E, E, T, T, E, F, E]), ([T, E, F, E, E, E, E, F, E, T, E, E, T, E, F], [T, E, F, E, E, E, E, F, E, T, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1054 (And.intro z_1922 (And.intro z_1923 trivial)))

theorem z_1925 : le (tf [T, E, F, E, E, E, E, F, T, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, E, F, T, E, E, E, T, E, F] [([E, T, F, E, E, E, E, F, T, E, E, E, T, E, F], [E, T, F, E, E, E, F, E, T, E, E, E, T, E, F]), ([T, E, F, E, E, E, E, F, E, T, E, E, T, E, F], [T, E, F, E, E, E, E, F, E, T, E, E, T, F, E]), ([T, E, F, E, E, E, E, F, T, E, E, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1067 (And.intro z_1923 (And.intro z_1575 trivial)))

theorem z_1926 : le (tf [T, E, E, F, E, E, E, F, T, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, F, T, E, E, T, E, E, F] [([E, T, E, F, E, E, E, F, T, E, E, T, E, E, F], [E, T, F, E, E, E, E, F, T, E, E, T, E, E, F]), ([T, E, E, F, E, E, E, F, E, T, E, T, E, E, F], [T, E, F, E, E, E, E, F, E, T, E, T, E, E, F]), ([T, E, E, F, E, E, E, F, T, E, E, E, T, E, F], [T, E, F, E, E, E, E, F, T, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1068 (And.intro z_1924 (And.intro z_1925 trivial)))

theorem z_1927 : le (tf [T, E, F, E, E, E, T, F, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, E, T, F, E, E, E, E, E, T, F] [([E, T, F, E, E, E, T, F, E, E, E, E, E, T, F], [E, T, F, E, E, F, T, E, E, E, E, E, E, T, F]), ([T, E, F, E, E, E, E, F, T, E, E, E, E, T, F], [T, F, E, E, E, E, E, F, T, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1264 (And.intro z_1575 trivial))

theorem z_1928 : le (tf [T, E, E, F, E, E, T, F, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, F, E, E, E, E, T, E, F] [([E, T, E, F, E, E, T, F, E, E, E, E, T, E, F], [E, T, F, E, E, E, T, F, E, E, E, E, T, E, F]), ([T, E, E, F, E, E, E, F, T, E, E, E, T, E, F], [T, E, F, E, E, E, E, F, T, E, E, E, T, E, F]), ([T, E, E, F, E, E, T, F, E, E, E, E, E, T, F], [T, E, F, E, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1265 (And.intro z_1925 (And.intro z_1927 trivial)))

theorem z_1929 : le (tf [T, E, E, E, F, E, T, F, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, F, E, E, E, T, E, E, F] [([E, T, E, E, F, E, T, F, E, E, E, T, E, E, F], [E, T, E, F, E, E, T, F, E, E, E, T, E, E, F]), ([T, E, E, E, F, E, E, F, T, E, E, T, E, E, F], [T, E, E, F, E, E, E, F, T, E, E, T, E, E, F]), ([T, E, E, E, F, E, T, F, E, E, E, E, T, E, F], [T, E, E, F, E, E, T, F, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1266 (And.intro z_1926 (And.intro z_1928 trivial)))

theorem z_1930 : le (tf [T, E, F, E, E, T, E, E, F, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, F, E, E, T, E, E, F, E, E, E, E, T, F] [([E, T, F, E, E, T, E, E, F, E, E, E, E, T, F], [E, T, F, E, E, T, E, F, E, E, E, E, E, T, F]), ([T, E, F, E, E, E, T, E, F, E, E, E, E, T, F], [T, E, F, E, E, E, T, F, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1269 (And.intro z_1927 trivial))

theorem z_1931 : le (tf [T, E, E, F, E, T, E, E, F, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, F, E, E, E, T, E, F] [([E, T, E, F, E, T, E, E, F, E, E, E, T, E, F], [E, T, F, E, E, T, E, E, F, E, E, E, T, E, F]), ([T, E, E, F, E, E, T, E, F, E, E, E, T, E, F], [T, E, E, F, E, E, T, F, E, E, E, E, T, E, F]), ([T, E, E, F, E, T, E, E, F, E, E, E, E, T, F], [T, E, F, E, E, T, E, E, F, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1270 (And.intro z_1928 (And.intro z_1930 trivial)))

theorem z_1932 : le (tf [T, E, E, E, F, T, E, E, F, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, T, E, E, F, E, E, T, E, E, F] [([E, T, E, E, F, T, E, E, F, E, E, T, E, E, F], [E, T, E, F, E, T, E, E, F, E, E, T, E, E, F]), ([T, E, E, E, F, E, T, E, F, E, E, T, E, E, F], [T, E, E, E, F, E, T, F, E, E, E, T, E, E, F]), ([T, E, E, E, F, T, E, E, F, E, E, E, T, E, F], [T, E, E, F, E, T, E, E, F, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1271 (And.intro z_1929 (And.intro z_1931 trivial)))

theorem z_1933 : le (tf [T, E, E, E, E, T, F, E, F, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, F, E, F, E, T, E, E, E, F] [([E, T, E, E, E, T, F, E, F, E, T, E, E, E, F], [E, T, E, E, F, T, E, E, F, E, T, E, E, E, F]), ([T, E, E, E, E, E, F, T, F, E, T, E, E, E, F], [T, E, E, E, E, F, E, T, F, E, T, E, E, E, F]), ([T, E, E, E, E, T, F, E, F, E, E, T, E, E, F], [T, E, E, E, F, T, E, E, F, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1558 (And.intro z_1920 (And.intro z_1932 trivial)))

theorem z_1934 : le (tf [T, E, E, E, E, T, F, E, T, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, F, E, T, F, E, E, E, E, F] [([E, T, E, E, E, T, F, E, T, F, E, E, E, E, F], [E, T, E, E, E, T, F, E, T, F, E, E, E, F, E]), ([T, E, E, E, E, E, F, T, T, F, E, E, E, E, F], [T, E, E, E, E, F, E, T, T, F, E, E, E, E, F]), ([T, E, E, E, E, T, F, E, E, F, T, E, E, E, F], [T, E, E, E, E, T, F, E, F, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1906 (And.intro z_1912 (And.intro z_1933 trivial)))

theorem z_1935 : le (tf [T, E, E, E, E, T, F, T, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, F, T, E, E, F, E, E, E, F] [([E, T, E, E, E, T, F, T, E, E, F, E, E, E, F], [E, T, E, E, E, T, F, T, E, F, E, E, E, E, F]), ([T, E, E, E, E, T, F, E, T, E, F, E, E, E, F], [T, E, E, E, E, T, F, E, T, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1907 (And.intro z_1934 trivial))

theorem z_1936 : le (tf [E, F, E, T, E, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, T, E, E, E, F, E, E, T, F] [([E, F, E, E, T, E, T, E, E, E, F, E, E, T, F], [F, E, E, E, T, E, T, E, E, E, F, E, E, T, F]), ([E, F, E, T, E, E, E, T, E, E, F, E, E, T, F], [F, E, E, T, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_859 (And.intro z_1032 trivial))

theorem z_1937 : le (tf [E, T, F, E, E, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, T, E, E, E, F, E, E, T, F] [([E, E, F, T, E, E, T, E, E, E, F, E, E, T, F], [E, F, E, T, E, E, T, E, E, E, F, E, E, T, F]), ([E, T, F, E, E, E, E, T, E, E, F, E, E, T, F], [F, T, E, E, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1936 (And.intro z_1090 trivial))

theorem z_1938 : le (tf [E, T, E, F, E, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, T, E, E, E, F, E, T, E, F] [([E, E, T, F, E, E, T, E, E, E, F, E, T, E, F], [E, F, T, E, E, E, T, E, E, E, F, E, T, E, F]), ([E, T, E, F, E, E, E, T, E, E, F, E, T, E, F], [E, T, F, E, E, E, E, T, E, E, F, E, T, E, F]), ([E, T, E, F, E, E, T, E, E, E, F, E, E, T, F], [E, T, F, E, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_965 (And.intro z_1091 (And.intro z_1937 trivial)))

theorem z_1939 : le (tf [E, T, E, E, F, E, T, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, T, E, E, E, F, T, E, E, F] [([E, E, T, E, F, E, T, E, E, E, F, T, E, E, F], [E, E, T, F, E, E, T, E, E, E, F, T, E, E, F]), ([E, T, E, E, F, E, E, T, E, E, F, T, E, E, F], [E, T, E, F, E, E, E, T, E, E, F, T, E, E, F]), ([E, T, E, E, F, E, T, E, E, E, F, E, T, E, F], [E, T, E, F, E, E, T, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_966 (And.intro z_1550 (And.intro z_1938 trivial)))

theorem z_1940 : le (tf [E, T, E, F, T, E, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, T, E, E, E, E, E, F, E, T, E, F] [([E, E, T, F, T, E, E, E, E, E, F, E, T, E, F], [E, E, T, F, T, E, E, E, E, F, E, E, T, E, F]), ([E, T, E, F, E, T, E, E, E, E, F, E, T, E, F], [E, T, F, E, E, T, E, E, E, E, F, E, T, E, F]), ([E, T, E, F, T, E, E, E, E, E, F, E, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_980 (And.intro z_1480 (And.intro z_1508 trivial)))

theorem z_1941 : le (tf [E, T, E, E, T, F, E, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, F, E, E, E, E, F, T, E, E, F] [([E, E, T, E, T, F, E, E, E, E, F, T, E, E, F], [E, E, T, F, T, E, E, E, E, E, F, T, E, E, F]), ([E, T, E, E, E, F, T, E, E, E, F, T, E, E, F], [E, T, E, E, F, E, T, E, E, E, F, T, E, E, F]), ([E, T, E, E, T, F, E, E, E, E, F, E, T, E, F], [E, T, E, F, T, E, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_981 (And.intro z_1939 (And.intro z_1940 trivial)))

theorem z_1942 : le (tf [E, T, E, E, T, E, F, E, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, E, F, E, E, T, F, E, E, E, F] [([E, E, T, E, T, E, F, E, E, T, F, E, E, E, F], [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F]), ([E, T, E, E, E, T, F, E, E, T, F, E, E, E, F], [E, T, E, E, E, T, F, E, F, T, E, E, E, E, F]), ([E, T, E, E, T, E, F, E, E, E, F, T, E, E, F], [E, T, E, E, T, F, E, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_982 (And.intro z_1559 (And.intro z_1941 trivial)))

theorem z_1943 : le (tf [T, E, E, F, E, E, T, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, T, E, E, E, F, E, E, T, F] [([E, T, E, F, E, E, T, E, E, E, F, E, E, T, F], [E, T, F, E, E, E, T, E, E, E, F, E, E, T, F]), ([T, E, E, F, E, E, E, T, E, E, F, E, E, T, F], [T, E, F, E, E, E, E, T, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1937 (And.intro z_1606 trivial))

theorem z_1944 : le (tf [T, E, E, E, F, E, T, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, T, E, E, E, F, E, T, E, F] [([E, T, E, E, F, E, T, E, E, E, F, E, T, E, F], [E, T, E, F, E, E, T, E, E, E, F, E, T, E, F]), ([T, E, E, E, F, E, E, T, E, E, F, E, T, E, F], [T, E, E, F, E, E, E, T, E, E, F, E, T, E, F]), ([T, E, E, E, F, E, T, E, E, E, F, E, E, T, F], [T, E, E, F, E, E, T, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1938 (And.intro z_1607 (And.intro z_1943 trivial)))

theorem z_1945 : le (tf [T, E, E, F, T, E, E, E, E, E, F, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, T, E, E, E, E, E, F, E, E, T, F] [([E, T, E, F, T, E, E, E, E, E, F, E, E, T, F], [E, T, F, E, T, E, E, E, E, E, F, E, E, T, F]), ([T, E, E, F, E, T, E, E, E, E, F, E, E, T, F], [T, E, F, E, E, T, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1508 (And.intro z_1616 trivial))

theorem z_1946 : le (tf [T, E, E, E, T, F, E, E, E, E, F, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, F, E, E, E, E, F, E, T, E, F] [([E, T, E, E, T, F, E, E, E, E, F, E, T, E, F], [E, T, E, F, T, E, E, E, E, E, F, E, T, E, F]), ([T, E, E, E, E, F, T, E, E, E, F, E, T, E, F], [T, E, E, E, F, E, T, E, E, E, F, E, T, E, F]), ([T, E, E, E, T, F, E, E, E, E, F, E, E, T, F], [T, E, E, F, T, E, E, E, E, E, F, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1940 (And.intro z_1944 (And.intro z_1945 trivial)))

theorem z_1947 : le (tf [T, E, E, E, T, E, F, E, E, E, F, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, F, E, E, E, F, T, E, E, F] [([E, T, E, E, T, E, F, E, E, E, F, T, E, E, F], [E, T, E, E, T, F, E, E, E, E, F, T, E, E, F]), ([T, E, E, E, E, T, F, E, E, E, F, T, E, E, F], [T, E, E, E, F, T, E, E, E, E, F, T, E, E, F]), ([T, E, E, E, T, E, F, E, E, E, F, E, T, E, F], [T, E, E, E, T, F, E, E, E, E, F, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1941 (And.intro z_1618 (And.intro z_1946 trivial)))

theorem z_1948 : le (tf [T, E, E, E, T, E, E, F, E, T, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, E, F, E, T, F, E, E, E, F] [([E, T, E, E, T, E, E, F, E, T, F, E, E, E, F], [E, T, E, E, T, E, F, E, E, T, F, E, E, E, F]), ([T, E, E, E, E, T, E, F, E, T, F, E, E, E, F], [T, E, E, E, E, T, F, E, E, T, F, E, E, E, F]), ([T, E, E, E, T, E, E, F, E, E, F, T, E, E, F], [T, E, E, E, T, E, F, E, E, E, F, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1942 (And.intro z_1619 (And.intro z_1947 trivial)))

theorem z_1949 : le (tf [T, E, E, E, T, E, E, T, F, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, E, T, F, E, F, E, E, E, F] [([E, T, E, E, T, E, E, T, F, E, F, E, E, E, F], [E, T, E, E, T, E, F, T, E, E, F, E, E, E, F]), ([T, E, E, E, E, T, E, T, F, E, F, E, E, E, F], [T, E, E, E, E, T, F, T, E, E, F, E, E, E, F]), ([T, E, E, E, T, E, E, E, F, T, F, E, E, E, F], [T, E, E, E, T, E, E, F, E, T, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1908 (And.intro z_1935 (And.intro z_1948 trivial)))

theorem z_1950 : le (tf [E, E, T, T, E, F, E, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, E, F, E, E, E, T, E, F, E, E, F] [([E, E, T, E, T, F, E, E, E, T, E, F, E, E, F], [E, E, T, E, T, F, E, E, E, T, F, E, E, E, F]), ([E, E, T, T, E, F, E, E, E, E, T, F, E, E, F], [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_982 (And.intro z_1013 trivial))

theorem z_1951 : le (tf [E, F, E, T, E, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, E, T, E, E, E, E, E, F, E, T, F] [([E, F, E, E, T, T, E, E, E, E, E, F, E, T, F], [F, E, E, E, T, T, E, E, E, E, E, F, E, T, F]), ([E, F, E, T, E, E, T, E, E, E, E, F, E, T, F], [F, E, E, T, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_986 (And.intro z_1096 trivial))

theorem z_1952 : le (tf [E, T, F, E, E, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, T, E, E, E, E, E, F, E, T, F] [([E, E, F, T, E, T, E, E, E, E, E, F, E, T, F], [E, F, E, T, E, T, E, E, E, E, E, F, E, T, F]), ([E, T, F, E, E, E, T, E, E, E, E, F, E, T, F], [F, T, E, E, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1951 (And.intro z_1138 trivial))

theorem z_1953 : le (tf [E, T, E, F, E, T, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, F, E, T, E, E, E, E, E, F, T, E, F] [([E, E, T, F, E, T, E, E, E, E, E, F, T, E, F], [E, F, T, E, E, T, E, E, E, E, E, F, T, E, F]), ([E, T, E, F, E, E, T, E, E, E, E, F, T, E, F], [E, T, F, E, E, E, T, E, E, E, E, F, T, E, F]), ([E, T, E, F, E, T, E, E, E, E, E, F, E, T, F], [E, T, F, E, E, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_999 (And.intro z_1139 (And.intro z_1952 trivial)))

theorem z_1954 : le (tf [E, T, E, T, F, E, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, F, E, E, E, E, E, E, F, T, E, F] [([E, E, T, T, F, E, E, E, E, E, E, F, T, E, F], [E, E, T, T, F, E, E, E, E, E, F, E, T, E, F]), ([E, T, E, E, F, T, E, E, E, E, E, F, T, E, F], [E, T, E, F, E, T, E, E, E, E, E, F, T, E, F]), ([E, T, E, T, F, E, E, E, E, E, E, F, E, T, F], [E, T, F, T, E, E, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1012 (And.intro z_1953 (And.intro z_1656 trivial)))

theorem z_1955 : le (tf [E, T, E, T, E, F, E, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, F, E, E, E, E, T, F, E, E, F] [([E, E, T, T, E, F, E, E, E, E, T, F, E, E, F], [E, E, T, T, F, E, E, E, E, E, T, F, E, E, F]), ([E, T, E, E, T, F, E, E, E, E, T, F, E, E, F], [E, T, E, E, T, F, E, E, E, F, T, E, E, E, F]), ([E, T, E, T, E, F, E, E, E, E, E, F, T, E, F], [E, T, E, T, F, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1013 (And.intro z_1277 (And.intro z_1954 trivial)))

theorem z_1956 : le (tf [E, T, E, T, E, E, F, E, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, E, F, E, E, T, E, F, E, E, F] [([E, E, T, T, E, E, F, E, E, T, E, F, E, E, F], [E, E, T, T, E, F, E, E, E, T, E, F, E, E, F]), ([E, T, E, E, T, E, F, E, E, T, E, F, E, E, F], [E, T, E, E, T, F, E, E, E, T, E, F, E, E, F]), ([E, T, E, T, E, E, F, E, E, E, T, F, E, E, F], [E, T, E, T, E, F, E, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1950 (And.intro z_1278 (And.intro z_1955 trivial)))

theorem z_1957 : le (tf [T, E, E, F, E, T, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, T, E, E, E, E, E, F, E, T, F] [([E, T, E, F, E, T, E, E, E, E, E, F, E, T, F], [E, T, F, E, E, T, E, E, E, E, E, F, E, T, F]), ([T, E, E, F, E, E, T, E, E, E, E, F, E, T, F], [T, E, F, E, E, E, T, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1952 (And.intro z_1624 trivial))

theorem z_1958 : le (tf [T, E, E, T, F, E, E, E, E, E, E, F, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, T, F, E, E, E, E, E, E, F, E, T, F] [([E, T, E, T, F, E, E, E, E, E, E, F, E, T, F], [E, T, F, T, E, E, E, E, E, E, E, F, E, T, F]), ([T, E, E, E, F, T, E, E, E, E, E, F, E, T, F], [T, E, E, F, E, T, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1656 (And.intro z_1957 trivial))

theorem z_1959 : le (tf [T, E, E, T, E, F, E, E, E, E, E, F, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, F, E, E, E, E, E, F, T, E, F] [([E, T, E, T, E, F, E, E, E, E, E, F, T, E, F], [E, T, E, T, F, E, E, E, E, E, E, F, T, E, F]), ([T, E, E, E, T, F, E, E, E, E, E, F, T, E, F], [T, E, E, F, T, E, E, E, E, E, E, F, T, E, F]), ([T, E, E, T, E, F, E, E, E, E, E, F, E, T, F], [T, E, E, T, F, E, E, E, E, E, E, F, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1954 (And.intro z_1628 (And.intro z_1958 trivial)))

theorem z_1960 : le (tf [T, E, E, T, E, E, F, E, E, E, T, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, F, E, E, E, T, F, E, E, F] [([E, T, E, T, E, E, F, E, E, E, T, F, E, E, F], [E, T, E, T, E, F, E, E, E, E, T, F, E, E, F]), ([T, E, E, E, T, E, F, E, E, E, T, F, E, E, F], [T, E, E, E, T, F, E, E, E, E, T, F, E, E, F]), ([T, E, E, T, E, E, F, E, E, E, E, F, T, E, F], [T, E, E, T, E, F, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1955 (And.intro z_1629 (And.intro z_1959 trivial)))

theorem z_1961 : le (tf [T, E, E, T, E, E, E, F, E, T, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, E, F, E, T, E, F, E, E, F] [([E, T, E, T, E, E, E, F, E, T, E, F, E, E, F], [E, T, E, T, E, E, F, E, E, T, E, F, E, E, F]), ([T, E, E, E, T, E, E, F, E, T, E, F, E, E, F], [T, E, E, E, T, E, E, F, E, T, F, E, E, E, F]), ([T, E, E, T, E, E, E, F, E, E, T, F, E, E, F], [T, E, E, T, E, E, F, E, E, E, T, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1956 (And.intro z_1948 (And.intro z_1960 trivial)))

theorem z_1962 : le (tf [T, E, E, T, E, E, E, T, F, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, E, T, F, E, E, F, E, E, F] [([E, T, E, T, E, E, E, T, F, E, E, F, E, E, F], [E, T, E, T, E, E, F, T, E, E, E, F, E, E, F]), ([T, E, E, E, T, E, E, T, F, E, E, F, E, E, F], [T, E, E, E, T, E, E, T, F, E, F, E, E, E, F]), ([T, E, E, T, E, E, E, E, F, T, E, F, E, E, F], [T, E, E, T, E, E, E, F, E, T, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1692 (And.intro z_1949 (And.intro z_1961 trivial)))

theorem z_1963 : le (tf [E, F, E, T, T, E, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, F, E, T, T, E, E, E, E, E, E, E, F, T, F] [([E, F, E, T, E, T, E, E, E, E, E, E, F, T, F], [F, E, E, T, E, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1493 trivial)

theorem z_1964 : le (tf [E, T, F, E, T, E, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, T, E, E, E, E, E, E, E, F, T, F] [([E, E, F, T, T, E, E, E, E, E, E, E, F, T, F], [E, F, E, T, T, E, E, E, E, E, E, E, F, T, F]), ([E, T, F, E, E, T, E, E, E, E, E, E, F, T, F], [F, T, E, E, E, T, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1963 (And.intro z_1495 trivial))

theorem z_1965 : le (tf [E, T, T, F, E, E, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [E, T, T, F, E, E, E, E, E, E, E, E, F, T, F] [([E, T, E, F, T, E, E, E, E, E, E, E, F, T, F], [E, T, F, E, T, E, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1964 trivial)

theorem z_1966 : le (tf [E, T, T, E, F, E, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, F, E, E, E, E, E, E, T, F, E, F] [([E, T, E, T, F, E, E, E, E, E, E, T, F, E, F], [E, T, E, T, F, E, E, E, E, E, F, T, E, E, F]), ([E, T, T, E, F, E, E, E, E, E, E, E, F, T, F], [E, T, T, F, E, E, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1484 (And.intro z_1965 trivial))

theorem z_1967 : le (tf [E, T, T, E, E, F, E, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, F, E, E, E, E, T, E, F, E, F] [([E, T, E, T, E, F, E, E, E, E, T, E, F, E, F], [E, T, E, T, F, E, E, E, E, E, T, E, F, E, F]), ([E, T, T, E, E, F, E, E, E, E, E, T, F, E, F], [E, T, T, E, F, E, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1500 (And.intro z_1966 trivial))

theorem z_1968 : le (tf [E, T, T, E, E, E, F, E, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, E, F, E, E, T, E, E, F, E, F] [([E, T, E, T, E, E, F, E, E, T, E, E, F, E, F], [E, T, E, T, E, E, F, E, E, T, E, F, E, E, F]), ([E, T, T, E, E, E, F, E, E, E, T, E, F, E, F], [E, T, T, E, E, F, E, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1956 (And.intro z_1967 trivial))

theorem z_1969 : le (tf [T, E, T, E, F, E, E, E, E, E, E, E, F, T, F]) zero :=
  le_zero_of_pairs [T, E, T, E, F, E, E, E, E, E, E, E, F, T, F] [([E, T, T, E, F, E, E, E, E, E, E, E, F, T, F], [E, T, T, F, E, E, E, E, E, E, E, E, F, T, F]), ([T, E, E, T, F, E, E, E, E, E, E, E, F, T, F], [T, E, F, T, E, E, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1965 (And.intro z_1657 trivial))

theorem z_1970 : le (tf [T, E, T, E, E, F, E, E, E, E, E, T, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, F, E, E, E, E, E, T, F, E, F] [([E, T, T, E, E, F, E, E, E, E, E, T, F, E, F], [E, T, T, E, F, E, E, E, E, E, E, T, F, E, F]), ([T, E, E, T, E, F, E, E, E, E, E, T, F, E, F], [T, E, E, T, F, E, E, E, E, E, E, T, F, E, F]), ([T, E, T, E, E, F, E, E, E, E, E, E, F, T, F], [T, E, T, E, F, E, E, E, E, E, E, E, F, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1966 (And.intro z_1658 (And.intro z_1969 trivial)))

theorem z_1971 : le (tf [T, E, T, E, E, E, F, E, E, E, T, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, F, E, E, E, T, E, F, E, F] [([E, T, T, E, E, E, F, E, E, E, T, E, F, E, F], [E, T, T, E, E, F, E, E, E, E, T, E, F, E, F]), ([T, E, E, T, E, E, F, E, E, E, T, E, F, E, F], [T, E, E, T, E, E, F, E, E, E, T, F, E, E, F]), ([T, E, T, E, E, E, F, E, E, E, E, T, F, E, F], [T, E, T, E, E, F, E, E, E, E, E, T, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1967 (And.intro z_1960 (And.intro z_1970 trivial)))

theorem z_1972 : le (tf [T, E, T, E, E, E, E, F, E, T, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, E, F, E, T, E, E, F, E, F] [([E, T, T, E, E, E, E, F, E, T, E, E, F, E, F], [E, T, T, E, E, E, F, E, E, T, E, E, F, E, F]), ([T, E, E, T, E, E, E, F, E, T, E, E, F, E, F], [T, E, E, T, E, E, E, F, E, T, E, F, E, E, F]), ([T, E, T, E, E, E, E, F, E, E, T, E, F, E, F], [T, E, T, E, E, E, F, E, E, E, T, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1968 (And.intro z_1961 (And.intro z_1971 trivial)))

theorem z_1973 : le (tf [T, E, T, E, E, E, E, T, F, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, E, T, F, E, E, E, F, E, F] [([E, T, T, E, E, E, E, T, F, E, E, E, F, E, F], [E, T, T, E, E, E, F, T, E, E, E, E, F, E, F]), ([T, E, E, T, E, E, E, T, F, E, E, E, F, E, F], [T, E, E, T, E, E, E, T, F, E, E, F, E, E, F]), ([T, E, T, E, E, E, E, E, F, T, E, E, F, E, F], [T, E, T, E, E, E, E, F, E, T, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1690 (And.intro z_1962 (And.intro z_1972 trivial)))

theorem z_1974 : le (tf [T, E, T, E, E, E, T, E, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, T, E, F, E, E, E, E, F, F] [([E, T, T, E, E, E, T, E, F, E, E, E, E, F, F], [E, T, T, E, E, E, T, F, E, E, E, E, E, F, F]), ([T, E, E, T, E, E, T, E, F, E, E, E, E, F, F], [T, E, E, T, E, E, T, F, E, E, E, E, E, F, F]), ([T, E, T, E, E, E, E, T, F, E, E, E, E, F, F], [T, E, T, E, E, E, E, T, F, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1517 (And.intro z_1662 (And.intro z_1973 trivial)))

theorem z_1975 : le (tf [T, E, T, E, E, T, E, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, T, E, E, E, F, E, E, E, F, F] [([E, T, T, E, E, T, E, E, E, F, E, E, E, F, F], [E, T, T, E, E, T, E, E, F, E, E, E, E, F, F]), ([T, E, E, T, E, T, E, E, E, F, E, E, E, F, F], [T, E, E, T, E, T, E, E, F, E, E, E, E, F, F]), ([T, E, T, E, E, E, T, E, E, F, E, E, E, F, F], [T, E, T, E, E, E, T, E, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1518 (And.intro z_1663 (And.intro z_1974 trivial)))

theorem z_1976 : le (tf [T, E, T, E, T, E, E, E, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, T, E, E, E, E, E, F, E, E, F, F] [([E, T, T, E, T, E, E, E, E, E, F, E, E, F, F], [E, T, T, E, T, E, E, E, E, F, E, E, E, F, F]), ([T, E, E, T, T, E, E, E, E, E, F, E, E, F, F], [T, E, E, T, T, E, E, E, E, F, E, E, E, F, F]), ([T, E, T, E, E, T, E, E, E, E, F, E, E, F, F], [T, E, T, E, E, T, E, E, E, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1519 (And.intro z_1664 (And.intro z_1975 trivial)))

theorem z_1977 : le (tf [T, E, T, T, E, E, E, E, E, E, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, T, E, E, E, E, E, E, E, F, E, F, F] [([E, T, T, T, E, E, E, E, E, E, E, F, E, F, F], [E, T, T, T, E, E, E, E, E, E, F, E, E, F, F]), ([T, E, T, E, T, E, E, E, E, E, E, F, E, F, F], [T, E, T, E, T, E, E, E, E, E, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1520 (And.intro z_1976 trivial))

theorem z_1978 : le (tf [T, E, T, F, E, E, E, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, E, T, F, E, E, E, E, E, E, E, E, T, F, F] [([E, T, T, F, E, E, E, E, E, E, E, E, T, F, F], [E, T, T, F, E, E, E, E, E, E, E, F, T, E, F]), ([T, E, E, F, T, E, E, E, E, E, E, E, T, F, F], [T, E, E, F, T, E, E, E, E, E, E, F, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1512 (And.intro z_1628 trivial))

theorem z_1979 : le (tf [T, T, E, E, F, E, E, E, E, E, E, E, T, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, F, E, E, E, E, E, E, E, T, F, F] [([T, E, T, E, F, E, E, E, E, E, E, E, T, F, F], [T, E, T, F, E, E, E, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1978 trivial)

theorem z_1980 : le (tf [T, T, E, E, E, F, E, E, E, E, E, T, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, F, E, E, E, E, E, T, E, F, F] [([T, E, T, E, E, F, E, E, E, E, E, T, E, F, F], [T, E, T, E, E, F, E, E, E, E, E, T, F, E, F]), ([T, T, E, E, E, F, E, E, E, E, E, E, T, F, F], [T, T, E, E, F, E, E, E, E, E, E, E, T, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1970 (And.intro z_1979 trivial))

theorem z_1981 : le (tf [T, T, E, E, E, E, F, E, E, E, T, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, F, E, E, E, T, E, E, F, F] [([T, E, T, E, E, E, F, E, E, E, T, E, E, F, F], [T, E, T, E, E, E, F, E, E, E, T, E, F, E, F]), ([T, T, E, E, E, E, F, E, E, E, E, T, E, F, F], [T, T, E, E, E, F, E, E, E, E, E, T, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1971 (And.intro z_1980 trivial))

theorem z_1982 : le (tf [T, T, E, E, E, E, E, F, E, T, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, E, F, E, T, E, E, E, F, F] [([T, E, T, E, E, E, E, F, E, T, E, E, E, F, F], [T, E, T, E, E, E, E, F, E, T, E, E, F, E, F]), ([T, T, E, E, E, E, E, F, E, E, T, E, E, F, F], [T, T, E, E, E, E, F, E, E, E, T, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1972 (And.intro z_1981 trivial))

theorem z_1983 : le (tf [T, T, E, E, E, E, E, T, F, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, E, T, F, E, E, E, E, F, F] [([T, E, T, E, E, E, E, T, F, E, E, E, E, F, F], [T, E, T, E, E, E, E, T, F, E, E, E, F, E, F]), ([T, T, E, E, E, E, E, E, F, T, E, E, E, F, F], [T, T, E, E, E, E, E, F, E, T, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1973 (And.intro z_1982 trivial))

theorem z_1984 : le (tf [T, T, E, E, E, E, T, E, E, F, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, E, T, E, E, F, E, E, E, F, F] [([T, E, T, E, E, E, T, E, E, F, E, E, E, F, F], [T, E, T, E, E, E, T, E, F, E, E, E, E, F, F]), ([T, T, E, E, E, E, E, T, E, F, E, E, E, F, F], [T, T, E, E, E, E, E, T, F, E, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1974 (And.intro z_1983 trivial))

theorem z_1985 : le (tf [T, T, E, E, E, T, E, E, E, E, F, E, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, E, T, E, E, E, E, F, E, E, F, F] [([T, E, T, E, E, T, E, E, E, E, F, E, E, F, F], [T, E, T, E, E, T, E, E, E, F, E, E, E, F, F]), ([T, T, E, E, E, E, T, E, E, E, F, E, E, F, F], [T, T, E, E, E, E, T, E, E, F, E, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1975 (And.intro z_1984 trivial))

theorem z_1986 : le (tf [T, T, E, E, T, E, E, E, E, E, E, F, E, F, F]) zero :=
  le_zero_of_pairs [T, T, E, E, T, E, E, E, E, E, E, F, E, F, F] [([T, E, T, E, T, E, E, E, E, E, E, F, E, F, F], [T, E, T, E, T, E, E, E, E, E, F, E, E, F, F]), ([T, T, E, E, E, T, E, E, E, E, E, F, E, F, F], [T, T, E, E, E, T, E, E, E, E, F, E, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1976 (And.intro z_1985 trivial))

theorem z_1987 : le (tf [T, T, E, T, E, E, E, E, E, E, E, E, F, F, F]) zero :=
  le_zero_of_pairs [T, T, E, T, E, E, E, E, E, E, E, E, F, F, F] [([T, E, T, T, E, E, E, E, E, E, E, E, F, F, F], [T, E, T, T, E, E, E, E, E, E, E, F, E, F, F]), ([T, T, E, E, T, E, E, E, E, E, E, E, F, F, F], [T, T, E, E, T, E, E, E, E, E, E, F, E, F, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1977 (And.intro z_1986 trivial))

theorem n_0 : UpperZero (tf [T, T, T, E, E, E, E, E, E, E, E, E, F, F, F]) :=
  upperZero_of_pairs [T, T, T, E, E, E, E, E, E, E, E, E, F, F, F] (lfZero_of_mirror_dec [T, T, T, E, E, E, E, E, E, E, E, E, F, F, F] (by decide +kernel)) [[T, T, E, T, E, E, E, E, E, E, E, E, F, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_1987 trivial)
    trivial

theorem infinitesimal : Infinitesimal (tf (start 3 9)) := by
  rw [infinitesimal_start_iff, show start 3 9 = [T, T, T, E, E, E, E, E, E, E, E, E, F, F, F] from by decide]
  exact n_0

end Cgt.Cert_3_9
