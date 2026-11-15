import Cgt.Certificate

/-! Machine-generated certificate: `T^2 □^17 F^2` is infinitesimal. -/

namespace Cgt.Cert_2_17
open Cell Game

theorem z_0 : le (tf [F, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_1 : le (tf [F, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T] [([F, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T], [F, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_0 trivial)

theorem z_2 : le (tf [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E] [([F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_3 : le (tf [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T] [([F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_1 trivial)

theorem z_4 : le (tf [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E] [([F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E], [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E]), ([F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_2 (And.intro z_3 trivial))

theorem z_5 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E] [([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 trivial)

theorem z_6 : le (tf [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T] [([F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_3 trivial)

theorem z_7 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E] [([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E]), ([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_4 (And.intro z_6 trivial))

theorem z_8 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, T, E, E], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E]), ([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_5 (And.intro z_7 trivial))

theorem z_9 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 trivial)

theorem z_10 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T] [([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_6 trivial)

theorem z_11 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E]), ([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_7 (And.intro z_10 trivial))

theorem z_12 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E]), ([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_8 (And.intro z_11 trivial))

theorem z_13 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, T, E, E, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_9 (And.intro z_12 trivial))

theorem z_14 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 trivial)

theorem z_15 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_10 trivial)

theorem z_16 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_11 (And.intro z_15 trivial))

theorem z_17 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_12 (And.intro z_16 trivial))

theorem z_18 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_13 (And.intro z_17 trivial))

theorem z_19 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_14 (And.intro z_18 trivial))

theorem z_20 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_15 trivial)

theorem z_21 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_16 (And.intro z_20 trivial))

theorem z_22 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_17 (And.intro z_21 trivial))

theorem z_23 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 (And.intro z_22 trivial))

theorem z_24 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_19 (And.intro z_23 trivial))

theorem z_25 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 trivial)

theorem z_26 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E, F, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 trivial)

theorem z_27 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_28 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, T], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_27 trivial)

theorem z_29 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, T, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_28 trivial)

theorem z_30 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_28 trivial)

theorem z_31 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, T, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, T, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_29 (And.intro z_30 trivial))

theorem z_32 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, T, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 trivial)

theorem z_33 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_30 trivial)

theorem z_34 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_31 (And.intro z_33 trivial))

theorem z_35 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_32 (And.intro z_34 trivial))

theorem z_36 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 trivial)

theorem z_37 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_33 trivial)

theorem z_38 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_34 (And.intro z_37 trivial))

theorem z_39 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_35 (And.intro z_38 trivial))

theorem z_40 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_36 (And.intro z_39 trivial))

theorem z_41 : le (tf [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T]) zero :=
  le_zero_of_pairs [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T] [] (by decide +kernel) (by decide +kernel)
    trivial

theorem z_42 : le (tf [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T] [([F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T], [F, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_41 trivial)

theorem z_43 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, E] [([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 trivial)

theorem z_44 : le (tf [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T] [([F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, T], [F, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_42 trivial)

theorem z_45 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, T, E], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, E]), ([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_43 (And.intro z_44 trivial))

theorem z_46 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, T, E, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 trivial)

theorem z_47 : le (tf [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T] [([F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, T], [F, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_44 trivial)

theorem z_48 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, E], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E]), ([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_45 (And.intro z_47 trivial))

theorem z_49 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, T, E, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, T, E, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_46 (And.intro z_48 trivial))

theorem z_50 : le (tf [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T] [([F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, T], [F, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_47 trivial)

theorem z_51 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, E], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_48 (And.intro z_50 trivial))

theorem z_52 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 (And.intro z_51 trivial))

theorem z_53 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_50 trivial)

theorem z_54 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_51 (And.intro z_53 trivial))

theorem z_55 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_52 (And.intro z_54 trivial))

theorem z_56 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_53 trivial)

theorem z_57 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_54 (And.intro z_56 trivial))

theorem z_58 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_55 (And.intro z_57 trivial))

theorem z_59 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_40 (And.intro z_58 trivial))

theorem z_60 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_37 trivial)

theorem z_61 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_38 (And.intro z_60 trivial))

theorem z_62 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_56 trivial)

theorem z_63 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_61 (And.intro z_62 trivial))

theorem z_64 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_58 (And.intro z_63 trivial))

theorem z_65 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_59 (And.intro z_64 trivial))

theorem z_66 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_65 trivial))

theorem z_67 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E, F, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 (And.intro z_66 trivial))

theorem z_68 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 trivial)

theorem z_69 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, T, E, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_49 trivial)

theorem z_70 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_69 (And.intro z_52 trivial))

theorem z_71 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 (And.intro z_55 trivial))

theorem z_72 : le (tf [F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_20 trivial)

theorem z_73 : le (tf [F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_21 (And.intro z_72 trivial))

theorem z_74 : le (tf [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_73 trivial))

theorem z_75 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_71 (And.intro z_74 trivial))

theorem z_76 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_24 (And.intro z_75 trivial))

theorem z_77 : le (tf [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_72 trivial)

theorem z_78 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_57 (And.intro z_77 trivial))

theorem z_79 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_74 (And.intro z_78 trivial))

theorem z_80 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 (And.intro z_79 trivial))

theorem z_81 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 (And.intro z_80 trivial))

theorem z_82 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_81 trivial))

theorem z_83 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_82 trivial))

theorem z_84 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 (And.intro z_83 trivial))

theorem z_85 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F] [([F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 trivial)

theorem z_86 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_62 trivial)

theorem z_87 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_63 (And.intro z_86 trivial))

theorem z_88 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_64 (And.intro z_87 trivial))

theorem z_89 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_86 trivial)

theorem z_90 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_87 (And.intro z_89 trivial))

theorem z_91 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 (And.intro z_90 trivial))

theorem z_92 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 (And.intro z_91 trivial))

theorem z_93 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_92 trivial))

theorem z_94 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_93 trivial))

theorem z_95 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F] [([F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_94 trivial))

theorem z_96 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F] [([E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_85 (And.intro z_95 trivial))

theorem z_97 : le (tf [E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, E, F] [([E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F], [E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 trivial)

theorem z_98 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 trivial)

theorem z_99 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_78 (And.intro z_98 trivial))

theorem z_100 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_99 trivial))

theorem z_101 : le (tf [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 (And.intro z_100 trivial))

theorem z_102 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_98 trivial)

theorem z_103 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_99 (And.intro z_102 trivial))

theorem z_104 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 (And.intro z_103 trivial))

theorem z_105 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_101 (And.intro z_104 trivial))

theorem z_106 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_105 trivial))

theorem z_107 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_106 trivial))

theorem z_108 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 (And.intro z_107 trivial))

theorem z_109 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F] [([E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_95 (And.intro z_108 trivial))

theorem z_110 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F] [([E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F], [E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F], [E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_96 (And.intro z_109 trivial))

theorem z_111 : le (tf [E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F] [([E, E, E, F, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, E, F], [E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, E, F]), ([E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F], [E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_97 (And.intro z_110 trivial))

theorem z_112 : le (tf [E, E, E, E, F, E, E, E, E, T, T, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, T, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 trivial)

theorem z_113 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_89 trivial)

theorem z_114 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 (And.intro z_113 trivial))

theorem z_115 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_113 trivial)

theorem z_116 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 (And.intro z_115 trivial))

theorem z_117 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_105 (And.intro z_116 trivial))

theorem z_118 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_117 trivial))

theorem z_119 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_118 trivial))

theorem z_120 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_108 (And.intro z_119 trivial))

theorem z_121 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, E, F] [([E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F], [E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_109 (And.intro z_120 trivial))

theorem z_122 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, E, F] [([E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F], [E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, E, F]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_110 (And.intro z_121 trivial))

theorem z_123 : le (tf [E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, E, E, E, E, F] [([E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, E, E, E, E, F], [E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_111 (And.intro z_122 trivial))

theorem z_124 : le (tf [E, E, E, E, E, F, E, E, T, E, T, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, T, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, F, E, E, E, E, T, T, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_112 (And.intro z_123 trivial))

theorem z_125 : le (tf [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, F, E, E, T, E, T, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_124 trivial)

theorem z_126 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 trivial)

theorem z_127 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_84 (And.intro z_94 trivial))

theorem z_128 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E] [([E, E, F, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E], [E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_126 (And.intro z_127 trivial))

theorem z_129 : le (tf [E, E, E, F, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F, E] [([E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 trivial)

theorem z_130 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_94 (And.intro z_107 trivial))

theorem z_131 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_127 (And.intro z_130 trivial))

theorem z_132 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E] [([E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, E, E, E, F, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_128 (And.intro z_131 trivial))

theorem z_133 : le (tf [E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E] [([E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F, E], [E, E, E, F, E, E, E, E, E, E, T, T, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_129 (And.intro z_132 trivial))

theorem z_134 : le (tf [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 trivial)

theorem z_135 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_107 (And.intro z_118 trivial))

theorem z_136 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_130 (And.intro z_135 trivial))

theorem z_137 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, E, E, E, F, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_131 (And.intro z_136 trivial))

theorem z_138 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E] [([E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, E, E, E, F, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_132 (And.intro z_137 trivial))

theorem z_139 : le (tf [E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_133 (And.intro z_138 trivial))

theorem z_140 : le (tf [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, F, E, E, T, T, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_134 (And.intro z_139 trivial))

theorem z_141 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_68 (And.intro z_83 trivial))

theorem z_142 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, F, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_141 trivial)

theorem z_143 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_83 (And.intro z_93 trivial))

theorem z_144 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_141 (And.intro z_143 trivial))

theorem z_145 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, E, F, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, T, E, E, E, E, E, F, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_142 (And.intro z_144 trivial))

theorem z_146 : le (tf [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 trivial)

theorem z_147 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_93 (And.intro z_106 trivial))

theorem z_148 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_143 (And.intro z_147 trivial))

theorem z_149 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_144 (And.intro z_148 trivial))

theorem z_150 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, E, E, E, F, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_145 (And.intro z_149 trivial))

theorem z_151 : le (tf [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_146 (And.intro z_150 trivial))

theorem z_152 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_106 (And.intro z_117 trivial))

theorem z_153 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_147 (And.intro z_152 trivial))

theorem z_154 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, E, E, E, F, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_148 (And.intro z_153 trivial))

theorem z_155 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_149 (And.intro z_154 trivial))

theorem z_156 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E, E, E, F, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_150 (And.intro z_155 trivial))

theorem z_157 : le (tf [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, F, E, E, T, E, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_151 (And.intro z_156 trivial))

theorem z_158 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, F, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 trivial)

theorem z_159 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_67 (And.intro z_82 trivial))

theorem z_160 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, E, F, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, T, E, E, E, F, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_158 (And.intro z_159 trivial))

theorem z_161 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_160 trivial)

theorem z_162 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_82 (And.intro z_92 trivial))

theorem z_163 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_159 (And.intro z_162 trivial))

theorem z_164 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_160 (And.intro z_163 trivial))

theorem z_165 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_161 (And.intro z_164 trivial))

theorem z_166 : le (tf [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E] [([F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E]), ([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 (And.intro z_114 trivial))

theorem z_167 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_92 (And.intro z_166 trivial))

theorem z_168 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_162 (And.intro z_167 trivial))

theorem z_169 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_163 (And.intro z_168 trivial))

theorem z_170 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, T, E, E, E, F, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_164 (And.intro z_169 trivial))

theorem z_171 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_165 (And.intro z_170 trivial))

theorem z_172 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_166 (And.intro z_116 trivial))

theorem z_173 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_167 (And.intro z_172 trivial))

theorem z_174 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, T, E, F, E, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_168 (And.intro z_173 trivial))

theorem z_175 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_169 (And.intro z_174 trivial))

theorem z_176 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E, E, F, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, T, E, E, E, F, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_170 (And.intro z_175 trivial))

theorem z_177 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_171 (And.intro z_176 trivial))

theorem z_178 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, E, F, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, T, E, F, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_26 (And.intro z_66 trivial))

theorem z_179 : le (tf [E, E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 trivial)

theorem z_180 : le (tf [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 (And.intro z_88 trivial))

theorem z_181 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_66 (And.intro z_180 trivial))

theorem z_182 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_178 (And.intro z_181 trivial))

theorem z_183 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_179 (And.intro z_182 trivial))

theorem z_184 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_180 (And.intro z_91 trivial))

theorem z_185 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_181 (And.intro z_184 trivial))

theorem z_186 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_182 (And.intro z_185 trivial))

theorem z_187 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_183 (And.intro z_186 trivial))

theorem z_188 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_91 (And.intro z_114 trivial))

theorem z_189 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_184 (And.intro z_188 trivial))

theorem z_190 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, T, F, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_185 (And.intro z_189 trivial))

theorem z_191 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, T, E, F, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_186 (And.intro z_190 trivial))

theorem z_192 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, F, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, E, T, E, E, F, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, E, F, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_187 (And.intro z_191 trivial))

theorem z_193 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_114 (And.intro z_115 trivial))

theorem z_194 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_188 (And.intro z_193 trivial))

theorem z_195 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_189 (And.intro z_194 trivial))

theorem z_196 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_190 (And.intro z_195 trivial))

theorem z_197 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, F, E, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, F, E, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_191 (And.intro z_196 trivial))

theorem z_198 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, F, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, F, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, F, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, F, E, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_192 (And.intro z_197 trivial))

theorem z_199 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_70 trivial)

theorem z_200 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_199 (And.intro z_71 trivial))

theorem z_201 : le (tf [F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E] [([F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E]), ([F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 (And.intro z_59 trivial))

theorem z_202 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 trivial)

theorem z_203 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_201 (And.intro z_65 trivial))

theorem z_204 : le (tf [E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_202 (And.intro z_203 trivial))

theorem z_205 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_65 (And.intro z_88 trivial))

theorem z_206 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_203 (And.intro z_205 trivial))

theorem z_207 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_204 (And.intro z_206 trivial))

theorem z_208 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_88 (And.intro z_90 trivial))

theorem z_209 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_205 (And.intro z_208 trivial))

theorem z_210 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_206 (And.intro z_209 trivial))

theorem z_211 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_207 (And.intro z_210 trivial))

theorem z_212 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_90 (And.intro z_113 trivial))

theorem z_213 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_208 (And.intro z_212 trivial))

theorem z_214 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_209 (And.intro z_213 trivial))

theorem z_215 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_210 (And.intro z_214 trivial))

theorem z_216 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, E, E, T, F, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, E, E, T, F, E, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_211 (And.intro z_215 trivial))

theorem z_217 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_113 trivial)

theorem z_218 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_212 (And.intro z_217 trivial))

theorem z_219 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_213 (And.intro z_218 trivial))

theorem z_220 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_214 (And.intro z_219 trivial))

theorem z_221 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_215 (And.intro z_220 trivial))

theorem z_222 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, F, E, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, F, E, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_216 (And.intro z_221 trivial))

theorem z_223 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_81 (And.intro z_101 trivial))

theorem z_224 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_101 (And.intro z_104 trivial))

theorem z_225 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_223 (And.intro z_224 trivial))

theorem z_226 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_102 trivial)

theorem z_227 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 (And.intro z_226 trivial))

theorem z_228 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_227 trivial))

theorem z_229 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_224 (And.intro z_228 trivial))

theorem z_230 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_225 (And.intro z_229 trivial))

theorem z_231 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 trivial)

theorem z_232 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E] [([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E]), ([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_231 trivial))

theorem z_233 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E] [([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_228 (And.intro z_232 trivial))

theorem z_234 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E] [([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_229 (And.intro z_233 trivial))

theorem z_235 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_230 (And.intro z_234 trivial))

theorem z_236 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T] [([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 trivial)

theorem z_237 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_232 (And.intro z_236 trivial))

theorem z_238 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E] [([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_233 (And.intro z_237 trivial))

theorem z_239 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E] [([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_234 (And.intro z_238 trivial))

theorem z_240 : le (tf [E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, T, E, E, E, E] [([E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_235 (And.intro z_239 trivial))

theorem z_241 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, F, E, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, E, E, T, F, E, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, F, E, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, T, E, E, E, E], [E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_222 (And.intro z_240 trivial))

theorem z_242 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, F, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, E, T, E, E, F, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, F, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, F, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, E, T, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_198 (And.intro z_241 trivial))

theorem z_243 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_177 (And.intro z_242 trivial))

theorem z_244 : le (tf [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_157 (And.intro z_243 trivial))

theorem z_245 : le (tf [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, E, F, T, E, T, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_140 (And.intro z_244 trivial))

theorem z_246 : le (tf [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, E, E, F, T, T, E, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_125 (And.intro z_245 trivial))

theorem z_247 : le (tf [E, E, E, E, E, E, T, T, F, E, E, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, T, F, E, E, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, E, T, E, F, T, E, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_246 trivial)

theorem z_248 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, T, E, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_25 (And.intro z_76 trivial))

theorem z_249 : le (tf [E, E, F, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 trivial)

theorem z_250 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_76 (And.intro z_80 trivial))

theorem z_251 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, T, E, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_248 (And.intro z_250 trivial))

theorem z_252 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, E, T, T, F, E, E, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_249 (And.intro z_251 trivial))

theorem z_253 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, T, E, F, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_252 trivial)

theorem z_254 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_80 (And.intro z_100 trivial))

theorem z_255 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_250 (And.intro z_254 trivial))

theorem z_256 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, T, E, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_251 (And.intro z_255 trivial))

theorem z_257 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_252 (And.intro z_256 trivial))

theorem z_258 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_253 (And.intro z_257 trivial))

theorem z_259 : le (tf [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_258 trivial)

theorem z_260 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_100 (And.intro z_103 trivial))

theorem z_261 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_254 (And.intro z_260 trivial))

theorem z_262 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_255 (And.intro z_261 trivial))

theorem z_263 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_256 (And.intro z_262 trivial))

theorem z_264 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_257 (And.intro z_263 trivial))

theorem z_265 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_258 (And.intro z_264 trivial))

theorem z_266 : le (tf [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E, F, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, T, E, E, E, E, F, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_259 (And.intro z_265 trivial))

theorem z_267 : le (tf [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 trivial)

theorem z_268 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E] [([E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E]), ([E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_103 (And.intro z_226 trivial))

theorem z_269 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_260 (And.intro z_268 trivial))

theorem z_270 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_261 (And.intro z_269 trivial))

theorem z_271 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_262 (And.intro z_270 trivial))

theorem z_272 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, T, E, E, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_263 (And.intro z_271 trivial))

theorem z_273 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, E, T, F, E, E, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_264 (And.intro z_272 trivial))

theorem z_274 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, F, E, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_265 (And.intro z_273 trivial))

theorem z_275 : le (tf [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, T, E, E, E, E, F, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_266 (And.intro z_274 trivial))

theorem z_276 : le (tf [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, F, E, E, T, T, E, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, F, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_267 (And.intro z_275 trivial))

theorem z_277 : le (tf [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_276 trivial)

theorem z_278 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, T, E, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 trivial)

theorem z_279 : le (tf [E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, T, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_200 (And.intro z_75 trivial))

theorem z_280 : le (tf [E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, E, F, T, T, E, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, T, E, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_278 (And.intro z_279 trivial))

theorem z_281 : le (tf [E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_75 (And.intro z_79 trivial))

theorem z_282 : le (tf [E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, T, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_279 (And.intro z_281 trivial))

theorem z_283 : le (tf [E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, T, E, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_280 (And.intro z_282 trivial))

theorem z_284 : le (tf [E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E] [([E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, T, E, E]), ([E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_79 (And.intro z_99 trivial))

theorem z_285 : le (tf [E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E] [([E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_281 (And.intro z_284 trivial))

theorem z_286 : le (tf [E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_282 (And.intro z_285 trivial))

theorem z_287 : le (tf [E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_283 (And.intro z_286 trivial))

theorem z_288 : le (tf [E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E] [([E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, T, E]), ([E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_99 (And.intro z_102 trivial))

theorem z_289 : le (tf [E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E] [([E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E]), ([E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_284 (And.intro z_288 trivial))

theorem z_290 : le (tf [E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E] [([E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E]), ([E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_285 (And.intro z_289 trivial))

theorem z_291 : le (tf [E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_286 (And.intro z_290 trivial))

theorem z_292 : le (tf [E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_287 (And.intro z_291 trivial))

theorem z_293 : le (tf [E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T] [([E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_102 trivial)

theorem z_294 : le (tf [E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E] [([E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E]), ([E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_288 (And.intro z_293 trivial))

theorem z_295 : le (tf [E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E] [([E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_289 (And.intro z_294 trivial))

theorem z_296 : le (tf [E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_290 (And.intro z_295 trivial))

theorem z_297 : le (tf [E, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E], [E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_291 (And.intro z_296 trivial))

theorem z_298 : le (tf [E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, T, E, E, E, E, E] [([E, E, E, E, E, E, F, E, E, T, E, E, E, F, E, T, E, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E]), ([E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, T, E, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_292 (And.intro z_297 trivial))

theorem z_299 : le (tf [E, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E] [([E, F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, T, E, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_14 (And.intro z_18 trivial))

theorem z_300 : le (tf [E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E] [([E, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, T, E, E, E]), ([E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_18 (And.intro z_22 trivial))

theorem z_301 : le (tf [E, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E] [([E, E, F, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E], [E, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, T, E, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_299 (And.intro z_300 trivial))

theorem z_302 : le (tf [E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E] [([E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E], [F, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E]), ([E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_22 (And.intro z_73 trivial))

theorem z_303 : le (tf [E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E] [([E, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E], [E, F, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E]), ([E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_300 (And.intro z_302 trivial))

theorem z_304 : le (tf [E, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E] [([E, E, E, F, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E], [E, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, T, E, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_301 (And.intro z_303 trivial))

theorem z_305 : le (tf [E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E] [([E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E], [F, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E]), ([E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_73 (And.intro z_77 trivial))

theorem z_306 : le (tf [E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E] [([E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E], [E, F, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E]), ([E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_302 (And.intro z_305 trivial))

theorem z_307 : le (tf [E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E] [([E, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E], [E, E, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E]), ([E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_303 (And.intro z_306 trivial))

theorem z_308 : le (tf [E, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, T, E, E, E, E] [([E, E, E, E, F, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E], [E, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, E, E]), ([E, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_304 (And.intro z_307 trivial))

theorem z_309 : le (tf [E, F, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T] [([E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_77 trivial)

theorem z_310 : le (tf [E, E, F, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E] [([E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E]), ([E, E, F, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_305 (And.intro z_309 trivial))

theorem z_311 : le (tf [E, E, E, F, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E] [([E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E]), ([E, E, E, F, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_306 (And.intro z_310 trivial))

theorem z_312 : le (tf [E, E, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E] [([E, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E]), ([E, E, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_307 (And.intro z_311 trivial))

theorem z_313 : le (tf [E, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E] [([E, E, E, E, E, F, E, E, E, E, F, T, E, E, E, E, T, E, E, E, E], [E, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, T, E, E, E, E]), ([E, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_308 (And.intro z_312 trivial))

theorem z_314 : le (tf [E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T] [([E, F, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_309 trivial)

theorem z_315 : le (tf [E, E, F, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E] [([E, E, F, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E]), ([E, E, F, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_310 (And.intro z_314 trivial))

theorem z_316 : le (tf [E, E, E, F, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E] [([E, E, E, F, E, E, E, E, E, T, E, F, E, E, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E]), ([E, E, E, F, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_311 (And.intro z_315 trivial))

theorem z_317 : le (tf [E, E, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E] [([E, E, E, E, F, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E]), ([E, E, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_312 (And.intro z_316 trivial))

theorem z_318 : le (tf [E, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, T, E, E, E, E] [([E, E, E, E, E, F, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E], [E, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E]), ([E, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_313 (And.intro z_317 trivial))

theorem z_319 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T] [([E, F, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_314 trivial)

theorem z_320 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E] [([E, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_315 (And.intro z_319 trivial))

theorem z_321 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E] [([E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_316 (And.intro z_320 trivial))

theorem z_322 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_317 (And.intro z_321 trivial))

theorem z_323 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E] [([E, E, E, E, E, F, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E], [E, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, T, E, E, E, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_318 (And.intro z_322 trivial))

theorem z_324 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T] [([E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, T], [E, F, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_319 trivial)

theorem z_325 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E] [([E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_320 (And.intro z_324 trivial))

theorem z_326 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E] [([E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_321 (And.intro z_325 trivial))

theorem z_327 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E] [([E, E, E, E, F, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_322 (And.intro z_326 trivial))

theorem z_328 : le (tf [E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, T, E, E, E, E] [([E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E, T, E, E, E, E], [E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E]), ([E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_323 (And.intro z_327 trivial))

theorem z_329 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, T, E, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, E, F, E, T, E, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, T, E, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, E, T, E, E, E, E], [E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_298 (And.intro z_328 trivial))

theorem z_330 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, E, T, F, E, E, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_273 (And.intro z_329 trivial))

theorem z_331 : le (tf [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, E, T, E, E, F, E, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, E, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_274 (And.intro z_330 trivial))

theorem z_332 : le (tf [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, E, E, E, F, T, E, E, T, E, E, E, E, F, E, E, E, E], [E, E, E, E, E, E, F, E, T, E, E, T, E, E, E, E, F, E, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_275 (And.intro z_331 trivial))

theorem z_333 : le (tf [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, E, F, T, E, T, E, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, F, E, T, E, T, E, E, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_276 (And.intro z_332 trivial))

theorem z_334 : le (tf [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, E, F, T, T, E, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, F, E, T, T, E, E, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_277 (And.intro z_333 trivial))

theorem z_335 : le (tf [E, E, E, E, E, E, T, F, T, E, E, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, E, T, F, T, E, E, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 trivial)

theorem z_336 : le (tf [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E] [([F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, T, E, E], [F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E]), ([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_104 (And.intro z_227 trivial))

theorem z_337 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E]), ([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_227 (And.intro z_231 trivial))

theorem z_338 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E, E] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E]), ([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, T, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_336 (And.intro z_337 trivial))

theorem z_339 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E]), ([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 (And.intro z_338 trivial))

theorem z_340 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E] [([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_118 (And.intro z_339 trivial))

theorem z_341 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E] [([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_135 (And.intro z_340 trivial))

theorem z_342 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_136 (And.intro z_341 trivial))

theorem z_343 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, T, E, E, E, E, E, F, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_137 (And.intro z_342 trivial))

theorem z_344 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E, E, E, E, F, E] [([E, E, E, E, E, F, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, E, F, E, E, E, T, E, E, E, T, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_138 (And.intro z_343 trivial))

theorem z_345 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 trivial)

theorem z_346 : le (tf [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E] [([F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E]), ([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_116 (And.intro z_345 trivial))

theorem z_347 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E] [([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E]), ([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_117 (And.intro z_346 trivial))

theorem z_348 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E] [([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_152 (And.intro z_347 trivial))

theorem z_349 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E] [([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, T, E, E, F, E, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_153 (And.intro z_348 trivial))

theorem z_350 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, T, E, E, E, F, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_154 (And.intro z_349 trivial))

theorem z_351 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, E, E, F, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_155 (And.intro z_350 trivial))

theorem z_352 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, T, E, F, E, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_174 (And.intro z_235 trivial))

theorem z_353 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_175 (And.intro z_352 trivial))

theorem z_354 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T] [([E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_115 trivial)

theorem z_355 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E] [([E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, T, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_193 (And.intro z_354 trivial))

theorem z_356 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E] [([E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, T, E, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_194 (And.intro z_355 trivial))

theorem z_357 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_195 (And.intro z_356 trivial))

theorem z_358 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E] [([E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, T, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_196 (And.intro z_357 trivial))

theorem z_359 : le (tf [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T] [([E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_236 trivial)

theorem z_360 : le (tf [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E] [([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E]), ([E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_237 (And.intro z_359 trivial))

theorem z_361 : le (tf [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E] [([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, F, E, T, E, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E]), ([E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_238 (And.intro z_360 trivial))

theorem z_362 : le (tf [E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E] [([E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, F, T, E, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E]), ([E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E], [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_239 (And.intro z_361 trivial))

theorem z_363 : le (tf [E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, F, E, E, E, E] [([E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, F, E, E, E, E], [E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E]), ([E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F, T, E, E, E], [E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_358 (And.intro z_362 trivial))

theorem z_364 : le (tf [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_353 (And.intro z_363 trivial))

theorem z_365 : le (tf [E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, E, E, E, F, T, E, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, E, F, E, T, E, E, E, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_351 (And.intro z_364 trivial))

theorem z_366 : le (tf [E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, F, T, E, E, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, E, E, F, E, T, E, E, E, E, T, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_344 (And.intro z_365 trivial))

theorem z_367 : le (tf [E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 (And.intro z_366 trivial))

theorem z_368 : le (tf [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_245 (And.intro z_367 trivial))

theorem z_369 : le (tf [E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, E, E, T, E, T, F, E, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, E, T, F, T, E, E, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_335 (And.intro z_368 trivial))

theorem z_370 : le (tf [E, E, E, E, E, T, E, T, E, F, E, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, T, E, F, E, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, E, T, T, E, F, E, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, E, T, T, F, E, E, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_247 (And.intro z_369 trivial))

theorem z_371 : le (tf [E, E, E, E, E, T, T, E, E, E, F, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, T, E, E, E, F, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, T, E, F, E, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 trivial)

theorem z_372 : le (tf [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T] [([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 trivial)

theorem z_373 : le (tf [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E] [([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, T, E, E]), ([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_338 (And.intro z_372 trivial))

theorem z_374 : le (tf [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F] [([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E]), ([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_339 (And.intro z_373 trivial))

theorem z_375 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, E, F] [([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, F], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_340 (And.intro z_374 trivial))

theorem z_376 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, E, F] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, E, F], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, E, F], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_341 (And.intro z_375 trivial))

theorem z_377 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, E, E, E, E, F] [([E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, E, F], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, E, F], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 (And.intro z_376 trivial))

theorem z_378 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, E, E, E, E, F] [([E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, E, E, F, E, E, T, E, E, E, E, E, T, E, E, E, E, E, F, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, E, E, E, E, E, F], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_343 (And.intro z_377 trivial))

theorem z_379 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E] [([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E]), ([E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_339 (And.intro z_373 trivial))

theorem z_380 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_340 (And.intro z_379 trivial))

theorem z_381 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, F, E] [([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, T, E, E, E, F, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_341 (And.intro z_380 trivial))

theorem z_382 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, E, E, F, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_342 (And.intro z_381 trivial))

theorem z_383 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E] [([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, T, E]), ([E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_346 (And.intro z_372 trivial))

theorem z_384 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E, E] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, T, F, E, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_347 (And.intro z_383 trivial))

theorem z_385 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E, E] [([E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, T, E, F, E, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_348 (And.intro z_384 trivial))

theorem z_386 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E, E] [([E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, T, E, E, F, E, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_349 (And.intro z_385 trivial))

theorem z_387 : le (tf [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T] [([E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_359 trivial)

theorem z_388 : le (tf [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E] [([E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T, E]), ([E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_360 (And.intro z_387 trivial))

theorem z_389 : le (tf [E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E] [([E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E], [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E, E]), ([E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_361 (And.intro z_388 trivial))

theorem z_390 : le (tf [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E] [([E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, T, E, E, E, E]), ([E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E], [E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_240 (And.intro z_389 trivial))

theorem z_391 : le (tf [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E] [([E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, T, E, E, F, E, E]), ([E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_386 (And.intro z_390 trivial))

theorem z_392 : le (tf [E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, E, E, E, F, T, E, E, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_382 (And.intro z_391 trivial))

theorem z_393 : le (tf [E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F] [([E, E, E, E, E, F, T, E, E, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, E, E, F, E, T, E, E, E, E, E, E, T, E, E, E, E, E, E, F]), ([E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, E, E, E, E, F], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_378 (And.intro z_392 trivial))

theorem z_394 : le (tf [E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E]), ([E, E, E, E, T, E, F, E, E, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_366 (And.intro z_393 trivial))

theorem z_395 : le (tf [E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, T, E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_367 (And.intro z_394 trivial))

theorem z_396 : le (tf [E, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_368 (And.intro z_395 trivial))

theorem z_397 : le (tf [E, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, E, T, F, E, E, E, E, E, E, E, E, E, F, E]), ([E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_369 (And.intro z_396 trivial))

theorem z_398 : le (tf [E, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, E, T, E, F, E, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, T, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_370 (And.intro z_397 trivial))

theorem z_399 : le (tf [E, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, F] [([E, E, E, E, E, T, T, E, E, E, E, F, E, E, E, E, E, E, E, E, F], [E, E, E, E, E, T, T, E, E, E, F, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, E, T, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_371 (And.intro z_398 trivial))

theorem z_400 : le (tf [E, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, F] [([E, E, E, E, T, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 trivial)

theorem z_401 : le (tf [E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T] [([E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T], [F, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_226 trivial)

theorem z_402 : le (tf [E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E] [([E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E], [E, F, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E]), ([E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_268 (And.intro z_401 trivial))

theorem z_403 : le (tf [E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E] [([E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E]), ([E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_269 (And.intro z_402 trivial))

theorem z_404 : le (tf [E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E] [([E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E]), ([E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_270 (And.intro z_403 trivial))

theorem z_405 : le (tf [E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E] [([E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E]), ([E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_271 (And.intro z_404 trivial))

theorem z_406 : le (tf [E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T] [([E, F, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_324 trivial)

theorem z_407 : le (tf [E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E] [([E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E]), ([E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_325 (And.intro z_406 trivial))

theorem z_408 : le (tf [E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E] [([E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E]), ([E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_326 (And.intro z_407 trivial))

theorem z_409 : le (tf [E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E] [([E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E]), ([E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_327 (And.intro z_408 trivial))

theorem z_410 : le (tf [E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E] [([E, E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E]), ([E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_405 (And.intro z_409 trivial))

theorem z_411 : le (tf [E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E] [([E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, T, E, E, E, E, E]), ([E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_329 (And.intro z_410 trivial))

theorem z_412 : le (tf [E, E, E, E, E, T, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, E, E, T, E, F, E, E, E, E, T, F, E, E, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_330 (And.intro z_411 trivial))

theorem z_413 : le (tf [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, F, E, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_331 (And.intro z_412 trivial))

theorem z_414 : le (tf [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E, F, E, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, F, E, E, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_332 (And.intro z_413 trivial))

theorem z_415 : le (tf [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, T, E, F, E, T, E, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, T, F, E, E, T, E, E, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_333 (And.intro z_414 trivial))

theorem z_416 : le (tf [E, E, E, E, E, T, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, T, E, F, T, E, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, T, F, E, T, E, E, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_334 (And.intro z_415 trivial))

theorem z_417 : le (tf [E, E, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_243 (And.intro z_365 trivial))

theorem z_418 : le (tf [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, E, T, E, F, E, E, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, E, T, F, E, E, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_244 (And.intro z_417 trivial))

theorem z_419 : le (tf [E, E, E, E, T, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E] [([E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_364 (And.intro z_391 trivial))

theorem z_420 : le (tf [E, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, E, T, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_365 (And.intro z_419 trivial))

theorem z_421 : le (tf [E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E] [([E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, T, E, E, E, E, E, F, E, E]), ([E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_417 (And.intro z_420 trivial))

theorem z_422 : le (tf [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E, E, F, E, E], [E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_418 (And.intro z_421 trivial))

theorem z_423 : le (tf [E, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E] [([E, E, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E], [E, E, E, E, E, T, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E]), ([E, E, E, E, T, E, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E], [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_416 (And.intro z_422 trivial))

theorem z_424 : le (tf [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T] [([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_372 trivial)

theorem z_425 : le (tf [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E] [([E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E]), ([E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_373 (And.intro z_424 trivial))

theorem z_426 : le (tf [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E] [([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, T, E, F, E]), ([E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_379 (And.intro z_425 trivial))

theorem z_427 : le (tf [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E] [([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_380 (And.intro z_426 trivial))

theorem z_428 : le (tf [E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T] [([E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 trivial)

theorem z_429 : le (tf [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E] [([E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E]), ([E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_388 (And.intro z_428 trivial))

theorem z_430 : le (tf [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E] [([E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E]), ([E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_362 (And.intro z_429 trivial))

theorem z_431 : le (tf [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E] [([E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_427 (And.intro z_430 trivial))

theorem z_432 : le (tf [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E] [([E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E, E]), ([E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_391 (And.intro z_431 trivial))

theorem z_433 : le (tf [E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, E, E, T, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_392 (And.intro z_432 trivial))

theorem z_434 : le (tf [E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E] [([E, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, E, T, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E, E]), ([E, E, E, T, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_420 (And.intro z_433 trivial))

theorem z_435 : le (tf [E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E] [([E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, E, T, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E, E]), ([E, E, E, T, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F, E], [E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_421 (And.intro z_434 trivial))

theorem z_436 : le (tf [E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E] [([E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E], [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E, E]), ([E, E, E, T, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E], [E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_422 (And.intro z_435 trivial))

theorem z_437 : le (tf [E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E] [([E, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E], [E, E, E, E, T, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E]), ([E, E, E, T, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, F, E], [E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_423 (And.intro z_436 trivial))

theorem z_438 : le (tf [E, E, E, T, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F] [([E, E, E, E, T, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_397 (And.intro z_437 trivial))

theorem z_439 : le (tf [E, E, E, T, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F] [([E, E, E, E, T, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, F]), ([E, E, E, T, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_398 (And.intro z_438 trivial))

theorem z_440 : le (tf [E, E, E, T, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F] [([E, E, E, E, T, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, E, E, T, E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, F]), ([E, E, E, T, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_399 (And.intro z_439 trivial))

theorem z_441 : le (tf [E, E, E, T, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, F] [([E, E, E, E, T, T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, F], [E, E, E, E, T, T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, F]), ([E, E, E, T, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F], [E, E, E, T, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_400 (And.intro z_440 trivial))

theorem z_442 : le (tf [E, E, E, T, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, E, T, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F] [([E, E, E, T, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, E, E, T, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 trivial)

theorem z_443 : le (tf [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, T] [([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_231 trivial)

theorem z_444 : le (tf [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E] [([F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, T, E], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E]), ([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_337 (And.intro z_443 trivial))

theorem z_445 : le (tf [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T] [([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_443 trivial)

theorem z_446 : le (tf [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E] [([F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E]), ([F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_444 (And.intro z_445 trivial))

theorem z_447 : le (tf [F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F] [([F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F], [F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_446 trivial)

theorem z_448 : le (tf [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F] [([E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]), ([E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F], [F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_425 (And.intro z_447 trivial))

theorem z_449 : le (tf [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F] [([E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E]), ([E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_426 (And.intro z_448 trivial))

theorem z_450 : le (tf [E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T] [([E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_428 trivial)

theorem z_451 : le (tf [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E] [([E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E]), ([E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_450 trivial))

theorem z_452 : le (tf [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F] [([E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F]), ([E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_449 (And.intro z_451 trivial))

theorem z_453 : le (tf [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F] [([E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F], [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_431 (And.intro z_452 trivial))

theorem z_454 : le (tf [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F] [([E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F], [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F, E]), ([E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F], [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_432 (And.intro z_453 trivial))

theorem z_455 : le (tf [E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F] [([E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F], [E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F, E]), ([E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, E, F], [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_433 (And.intro z_454 trivial))

theorem z_456 : le (tf [E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F, E]), ([E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, E, F], [E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_434 (And.intro z_455 trivial))

theorem z_457 : le (tf [E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E]), ([E, E, T, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_435 (And.intro z_456 trivial))

theorem z_458 : le (tf [E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E]), ([E, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_436 (And.intro z_457 trivial))

theorem z_459 : le (tf [E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E]), ([E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_437 (And.intro z_458 trivial))

theorem z_460 : le (tf [E, E, T, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, F]), ([E, E, T, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_438 (And.intro z_459 trivial))

theorem z_461 : le (tf [E, E, T, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F] [([E, E, E, T, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, E, T, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, F]), ([E, E, T, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_439 (And.intro z_460 trivial))

theorem z_462 : le (tf [E, E, T, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F] [([E, E, E, T, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F], [E, E, E, T, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, F]), ([E, E, T, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_440 (And.intro z_461 trivial))

theorem z_463 : le (tf [E, E, T, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F] [([E, E, E, T, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, E, E, T, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, F]), ([E, E, T, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, E, T, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_441 (And.intro z_462 trivial))

theorem z_464 : le (tf [E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F] [([E, E, E, T, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F], [E, E, E, T, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F]), ([E, E, T, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F], [E, E, T, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_442 (And.intro z_463 trivial))

theorem z_465 : le (tf [E, E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F] [([E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F], [E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_464 trivial)

theorem z_466 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, T] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, F, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_401 trivial)

theorem z_467 : le (tf [E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E] [([E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E]), ([E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_402 (And.intro z_466 trivial))

theorem z_468 : le (tf [E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E] [([E, E, E, E, F, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, F, E, E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E]), ([E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, E, F, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_403 (And.intro z_467 trivial))

theorem z_469 : le (tf [E, E, F, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T] [([E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, F, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_406 trivial)

theorem z_470 : le (tf [E, E, E, F, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, F, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E] [([E, E, E, F, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E]), ([E, E, E, F, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T], [E, E, F, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_407 (And.intro z_469 trivial))

theorem z_471 : le (tf [E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E] [([E, E, E, E, E, F, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, E, F, E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E]), ([E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E], [E, E, E, F, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_468 (And.intro z_470 trivial))

theorem z_472 : le (tf [E, E, E, E, T, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E] [([E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, E, F, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E]), ([E, E, E, E, T, E, F, E, E, E, E, E, E, E, F, E, E, E, T, E, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_409 (And.intro z_471 trivial))

theorem z_473 : le (tf [E, E, E, E, T, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E] [([E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E, T, E, E, E, E]), ([E, E, E, E, T, E, E, F, E, E, E, E, E, E, F, E, E, T, E, E, E], [E, E, E, E, T, E, F, E, E, E, E, E, E, E, F, E, E, T, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_410 (And.intro z_472 trivial))

theorem z_474 : le (tf [E, E, E, E, T, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E] [([E, E, E, E, E, T, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, E, E, F, T, E, E, E, E, E]), ([E, E, E, E, T, E, E, E, F, E, E, E, E, E, F, E, T, E, E, E, E], [E, E, E, E, T, E, E, F, E, E, E, E, E, E, F, E, T, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_411 (And.intro z_473 trivial))

theorem z_475 : le (tf [E, E, E, E, T, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, E] [([E, E, E, E, E, T, E, E, E, F, E, E, E, T, F, E, E, E, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, E, E, T, F, E, E, E, E, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, E, E, E, F, T, E, E, E, E, E], [E, E, E, E, T, E, E, E, F, E, E, E, E, E, F, T, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_412 (And.intro z_474 trivial))

theorem z_476 : le (tf [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, E] [([E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, F, E, E, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, F, E, E, E, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, F, E, E, E, E, E], [E, E, E, E, T, E, E, E, E, F, E, E, E, T, F, E, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_413 (And.intro z_475 trivial))

theorem z_477 : le (tf [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, E] [([E, E, E, E, E, T, E, E, E, F, E, T, E, E, E, E, F, E, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, T, E, E, E, E, F, E, E, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E, F, E, E, E, E], [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, F, E, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_414 (And.intro z_476 trivial))

theorem z_478 : le (tf [E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, E] [([E, E, E, E, E, T, E, E, E, F, T, E, E, E, E, E, E, F, E, E, E], [E, E, E, E, E, T, E, E, F, E, T, E, E, E, E, E, E, F, E, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E, E], [E, E, E, E, T, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_415 (And.intro z_477 trivial))

theorem z_479 : le (tf [E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E] [([E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, E, T, E, E, F, E, E, E, E]), ([E, E, E, E, E, T, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_242 (And.intro z_364 trivial))

theorem z_480 : le (tf [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, E, E, T, E, F, E, E, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, E, E, T, F, E, E, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_243 (And.intro z_479 trivial))

theorem z_481 : le (tf [E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E] [([E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, T, F, E, E, E, E]), ([E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_363 (And.intro z_390 trivial))

theorem z_482 : le (tf [E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, E, E, T, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, E, T, F, E, E, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_364 (And.intro z_481 trivial))

theorem z_483 : le (tf [E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E] [([E, E, E, E, E, T, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, E, T, E, F, E, E, E, E, E, T, E, E, E, F, E, E, E]), ([E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_479 (And.intro z_482 trivial))

theorem z_484 : le (tf [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, E, T, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, E, T, E, E, F, E, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_480 (And.intro z_483 trivial))

theorem z_485 : le (tf [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T] [([E, F, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T], [F, E, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_345 trivial)

theorem z_486 : le (tf [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E] [([E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, T, E]), ([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_355 (And.intro z_485 trivial))

theorem z_487 : le (tf [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T] [([E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, F, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_485 trivial)

theorem z_488 : le (tf [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E] [([E, E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, F, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, T, E]), ([E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_486 (And.intro z_487 trivial))

theorem z_489 : le (tf [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T]) zero :=
  le_zero_of_pairs [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T] [([E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_387 trivial)

theorem z_490 : le (tf [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E]) zero :=
  le_zero_of_pairs [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E] [([E, E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E]), ([E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T], [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_488 (And.intro z_489 trivial))

theorem z_491 : le (tf [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E] [([E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E], [E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E]), ([E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E], [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_389 (And.intro z_490 trivial))

theorem z_492 : le (tf [E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E] [([E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E, E]), ([E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, F, T, E, E], [E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, F, T, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_390 (And.intro z_491 trivial))

theorem z_493 : le (tf [E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E] [([E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E, E]), ([E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, T, F, E, E, E], [E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_481 (And.intro z_492 trivial))

theorem z_494 : le (tf [E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E] [([E, E, E, E, T, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, E, T, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, T, E, F, E, E, E], [E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_482 (And.intro z_493 trivial))

theorem z_495 : le (tf [E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E] [([E, E, E, E, T, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E], [E, E, E, E, T, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E, E]), ([E, E, E, T, E, E, E, E, E, F, E, E, E, E, T, E, E, F, E, E, E], [E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_483 (And.intro z_494 trivial))

theorem z_496 : le (tf [E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E] [([E, E, E, E, T, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E], [E, E, E, E, T, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E, E]), ([E, E, E, T, E, E, E, E, E, E, F, E, E, T, E, E, E, F, E, E, E], [E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_484 (And.intro z_495 trivial))

theorem z_497 : le (tf [E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, E, E]) zero :=
  le_zero_of_pairs [E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, E, E] [([E, E, E, E, T, E, E, E, E, E, T, F, E, E, E, E, E, F, E, E, E], [E, E, E, E, T, E, E, E, E, F, T, E, E, E, E, E, E, F, E, E, E]), ([E, E, E, T, E, E, E, E, E, E, E, F, T, E, E, E, E, F, E, E, E], [E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_478 (And.intro z_496 trivial))

theorem z_498 : le (tf [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T] [([E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [E, E, F, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_487 trivial)

theorem z_499 : le (tf [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T]) zero :=
  le_zero_of_pairs [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T] [([E, E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [E, E, F, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_498 trivial)

theorem z_500 : le (tf [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E]) zero :=
  le_zero_of_pairs [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E] [([E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E]), ([E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T], [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 (And.intro z_499 trivial))

theorem z_501 : le (tf [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E] [([E, E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E]), ([E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E], [E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_430 (And.intro z_500 trivial))

theorem z_502 : le (tf [E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E] [([E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, T, F, E, E, E]), ([E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, F, E, E], [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_492 (And.intro z_501 trivial))

theorem z_503 : le (tf [E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E] [([E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, T, E, F, E, E, E]), ([E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, F, E, E], [E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_493 (And.intro z_502 trivial))

theorem z_504 : le (tf [E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E] [([E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E], [E, E, E, T, E, E, E, E, F, E, E, E, E, E, T, E, E, F, E, E, E]), ([E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, F, E, E], [E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_494 (And.intro z_503 trivial))

theorem z_505 : le (tf [E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E] [([E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E], [E, E, E, T, E, E, E, E, E, F, E, E, E, T, E, E, E, F, E, E, E]), ([E, E, T, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, F, E, E], [E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_495 (And.intro z_504 trivial))

theorem z_506 : le (tf [E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E] [([E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E], [E, E, E, T, E, E, E, E, E, E, F, E, T, E, E, E, E, F, E, E, E]), ([E, E, T, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, F, E, E], [E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_496 (And.intro z_505 trivial))

theorem z_507 : le (tf [E, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, E, E]) zero :=
  le_zero_of_pairs [E, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, E, E] [([E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, E, E], [E, E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, F, E, E, E]), ([E, E, T, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, F, E, E], [E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_497 (And.intro z_506 trivial))

theorem z_508 : le (tf [E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T]) zero :=
  le_zero_of_pairs [E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T] [([E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_450 trivial)

theorem z_509 : le (tf [E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E] [([E, E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [E, E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]), ([E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T], [E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T])] (by decide +kernel) (by decide +kernel)
    (And.intro z_451 (And.intro z_508 trivial))

theorem z_510 : le (tf [E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E] [([E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, F, E, E]), ([E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E], [E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_501 (And.intro z_509 trivial))

theorem z_511 : le (tf [E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E] [([E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, F, E, E]), ([E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, F, E], [E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_502 (And.intro z_510 trivial))

theorem z_512 : le (tf [E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E] [([E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E], [E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, F, E, E]), ([E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, F, E], [E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_503 (And.intro z_511 trivial))

theorem z_513 : le (tf [E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E] [([E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E], [E, E, T, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, F, E, E]), ([E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, F, E], [E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_504 (And.intro z_512 trivial))

theorem z_514 : le (tf [E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E] [([E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E], [E, E, T, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, F, E, E]), ([E, T, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, F, E], [E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_505 (And.intro z_513 trivial))

theorem z_515 : le (tf [E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E] [([E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E], [E, E, T, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, F, E, E]), ([E, T, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, F, E], [E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_506 (And.intro z_514 trivial))

theorem z_516 : le (tf [E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E] [([E, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E], [E, E, T, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, F, E, E]), ([E, T, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, F, E], [E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_507 (And.intro z_515 trivial))

theorem z_517 : le (tf [E, T, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F] [([E, E, T, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, E, F]), ([E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_459 (And.intro z_516 trivial))

theorem z_518 : le (tf [E, T, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F] [([E, E, T, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, E, F]), ([E, T, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_460 (And.intro z_517 trivial))

theorem z_519 : le (tf [E, T, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F] [([E, E, T, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F], [E, E, T, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, E, F]), ([E, T, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_461 (And.intro z_518 trivial))

theorem z_520 : le (tf [E, T, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F] [([E, E, T, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, E, T, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, E, F]), ([E, T, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, T, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_462 (And.intro z_519 trivial))

theorem z_521 : le (tf [E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F] [([E, E, T, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F], [E, E, T, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, E, F]), ([E, T, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, F], [E, T, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_463 (And.intro z_520 trivial))

theorem z_522 : le (tf [E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F] [([E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F], [E, E, T, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F]), ([E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F], [E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_464 (And.intro z_521 trivial))

theorem z_523 : le (tf [E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F] [([E, E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F], [E, E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F]), ([E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F], [E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_465 (And.intro z_522 trivial))

theorem z_524 : le (tf [E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F] [([E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F], [E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 trivial)

theorem z_525 : le (tf [E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F] [([E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F], [E, E, F, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, T, E])] (by decide +kernel) (by decide +kernel)
    (And.intro z_429 trivial)

theorem z_526 : le (tf [T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F]) zero :=
  le_zero_of_pairs [T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F] [([E, T, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F], [E, T, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_525 trivial)

theorem z_527 : le (tf [T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F] [([E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [E, T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F, E]), ([T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F], [T, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, T, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_509 (And.intro z_526 trivial))

theorem z_528 : le (tf [T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F] [([E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [E, T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, F, E]), ([T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F], [T, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, E, E, T, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_510 (And.intro z_527 trivial))

theorem z_529 : le (tf [T, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F] [([E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F], [E, T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, F, E]), ([T, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, T, E, E, F], [T, E, E, E, E, F, E, E, E, E, E, E, E, E, E, E, E, T, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_511 (And.intro z_528 trivial))

theorem z_530 : le (tf [T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F] [([E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F], [E, T, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, F, E]), ([T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, E, T, E, E, E, F], [T, E, E, E, E, E, F, E, E, E, E, E, E, E, E, E, T, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_512 (And.intro z_529 trivial))

theorem z_531 : le (tf [T, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, F, E]), ([T, E, E, E, E, E, E, E, F, E, E, E, E, E, E, T, E, E, E, E, F], [T, E, E, E, E, E, E, F, E, E, E, E, E, E, E, T, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_513 (And.intro z_530 trivial))

theorem z_532 : le (tf [T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, F, E]), ([T, E, E, E, E, E, E, E, E, F, E, E, E, E, T, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, F, E, E, E, E, E, T, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_514 (And.intro z_531 trivial))

theorem z_533 : le (tf [T, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, F, E]), ([T, E, E, E, E, E, E, E, E, E, F, E, E, T, E, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, E, F, E, E, E, T, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_515 (And.intro z_532 trivial))

theorem z_534 : le (tf [T, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, F, E]), ([T, E, E, E, E, E, E, E, E, E, E, F, T, E, E, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, E, E, F, E, T, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_516 (And.intro z_533 trivial))

theorem z_535 : le (tf [T, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, E, F]), ([T, E, E, E, E, E, E, E, E, E, T, E, F, E, E, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, E, E, T, F, E, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_517 (And.intro z_534 trivial))

theorem z_536 : le (tf [T, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, F] [([E, T, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, F], [E, T, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, E, F]), ([T, E, E, E, E, E, E, E, E, T, E, E, E, F, E, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, E, T, E, E, F, E, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_518 (And.intro z_535 trivial))

theorem z_537 : le (tf [T, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, F] [([E, T, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, F], [E, T, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, E, F]), ([T, E, E, E, E, E, E, E, T, E, E, E, E, E, F, E, E, E, E, E, F], [T, E, E, E, E, E, E, E, T, E, E, E, E, F, E, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_519 (And.intro z_536 trivial))

theorem z_538 : le (tf [T, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, F] [([E, T, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, F], [E, T, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, E, F]), ([T, E, E, E, E, E, E, T, E, E, E, E, E, E, E, F, E, E, E, E, F], [T, E, E, E, E, E, E, T, E, E, E, E, E, E, F, E, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_520 (And.intro z_537 trivial))

theorem z_539 : le (tf [T, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F] [([E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F], [E, T, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, E, F]), ([T, E, E, E, E, E, T, E, E, E, E, E, E, E, E, E, F, E, E, E, F], [T, E, E, E, E, E, T, E, E, E, E, E, E, E, E, F, E, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_521 (And.intro z_538 trivial))

theorem z_540 : le (tf [T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F]) zero :=
  le_zero_of_pairs [T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F] [([E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F], [E, T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F]), ([T, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F], [T, E, E, E, E, T, E, E, E, E, E, E, E, E, E, E, F, E, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_522 (And.intro z_539 trivial))

theorem z_541 : le (tf [T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F]) zero :=
  le_zero_of_pairs [T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F] [([E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F], [E, T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F]), ([T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F], [T, E, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, F, E, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_523 (And.intro z_540 trivial))

theorem z_542 : le (tf [T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F]) zero :=
  le_zero_of_pairs [T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F] [([E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F], [E, T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F]), ([T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F], [T, E, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, E, F])] (by decide +kernel) (by decide +kernel)
    (And.intro z_524 (And.intro z_541 trivial))

theorem n_0 : UpperZero (tf [T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F]) :=
  upperZero_of_pairs [T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F] (lfZero_of_mirror_dec [T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F] (by decide +kernel)) [[T, E, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F]] []
    (by decide +kernel) (by decide +kernel)
    (And.intro z_542 trivial)
    trivial

theorem infinitesimal : Infinitesimal (tf (start 2 17)) := by
  rw [infinitesimal_start_iff, show start 2 17 = [T, T, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, E, F, F] from by decide]
  exact n_0

end Cgt.Cert_2_17
