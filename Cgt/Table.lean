import Cgt.RowA2Values

/-!
# Strategy tables for single positions

A strategy for Right, proving `X ≤ 0` or `X ≤ ∗` for a concrete position, given as tables of
positions: `N` (positions claimed `≤ 0`) and `S` (positions claimed `≤ ∗`). The check is local:

* a position of `N`: every Left move has a Right reply in `N`;
* a position of `S`: some Right move is in `N` (Right's answer when Left takes the `∗`), and every
  Left move is in `N` (Right then takes the `∗`) or has a Right reply in `S`.

`soundN` and `soundS` show that the check makes every claim true. They hold for any tables: the
lookup only has to be *sound* (`look t x = true → x ∈ t`), which it is by construction, since it
compares the entry it finds with `x`. How it searches (binary search over a sorted array) does not
matter for the proof.

Positions are encoded as natural numbers, two bits per cell after a leading `1` (`encode`), so
that a table is an `Array Nat`.
-/

namespace Cgt
open Cell TF Game

namespace Table

/-- The code of a cell. -/
def cellCode : Cell → Nat
  | E => 0
  | T => 1
  | F => 2

/-- A position as a natural number: two bits per cell, the first cell lowest, after a leading `1`. -/
def encode : List Cell → Nat
  | [] => 1
  | c :: p => encode p * 4 + cellCode c

/-- The cell with a given code. -/
def cellOf (k : Nat) : Cell := if k = 1 then T else if k = 2 then F else E

/-- The inverse of `encode`. -/
def decode (n : Nat) : List Cell :=
  if h : n ≤ 1 then [] else cellOf (n % 4) :: decode (n / 4)
termination_by n
decreasing_by omega

theorem one_le_encode : ∀ p : List Cell, 1 ≤ encode p
  | [] => Nat.le_refl 1
  | _ :: p => by have := one_le_encode p; simp only [encode]; omega

theorem decode_encode : ∀ p : List Cell, decode (encode p) = p
  | [] => by simp [encode, decode]
  | c :: p => by
    have h1 := one_le_encode p
    rw [decode]
    split
    · simp only [encode] at *; omega
    have hc : cellCode c < 4 := by cases c <;> simp [cellCode]
    have hm : (encode p * 4 + cellCode c) % 4 = cellCode c := by omega
    have hd : (encode p * 4 + cellCode c) / 4 = encode p := by omega
    simp only [encode, hm, hd, decode_encode p]
    cases c <;> simp [cellOf, cellCode]

/-- Binary search for `x` in a sorted array (fuel-bounded); returns an index to compare. -/
def bfind (t : Array Nat) (x : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 ≥ hi then lo
    else
      let mid := (lo + hi) / 2
      if t[mid]?.getD 0 ≤ x then bfind t x fuel mid hi else bfind t x fuel lo mid

/-- Is `x` in the sorted array `t`? Sound for any array: it compares the entry it finds. -/
def look (t : Array Nat) (x : Nat) : Bool := t[bfind t x 64 0 t.size]? == some x

theorem mem_of_look {t : Array Nat} {x : Nat} (h : look t x = true) : x ∈ t := by
  unfold look at h
  exact Array.mem_of_getElem? (by simpa using h)

/-- Membership of a position. -/
def mem (t : Array Nat) (p : List Cell) : Bool := look t (encode p)

/-- The check of a position claimed `≤ 0`. -/
def chkN (tn : Array Nat) (p : List Cell) : Bool :=
  (leftMoves p).all fun q => (rightMoves q).any (mem tn)

/-- The check of a position claimed `≤ ∗`. -/
def chkS (ts tn : Array Nat) (p : List Cell) : Bool :=
  (rightMoves p).any (mem tn) &&
    (leftMoves p).all fun q => mem tn q || (rightMoves q).any (mem ts)

theorem soundN_aux (tn : Array Nat) (h : ∀ x ∈ tn, chkN tn (decode x) = true) :
    ∀ n, ∀ p : List Cell, pot p < n → mem tn p = true → le (tf p) zero
  | 0, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, p, hp, hm => by
    have hc := h _ (mem_of_look hm)
    rw [decode_encode] at hc
    rw [le_zero_iff_tf]
    intro q hq
    simp only [chkN, List.all_eq_true, List.any_eq_true] at hc
    obtain ⟨r, hr, hmr⟩ := hc q hq
    have h1 := pot_lt_of_mem_leftMoves hq
    have h2 := pot_lt_of_mem_rightMoves hr
    exact ⟨r, hr, soundN_aux tn h n r (by omega) hmr⟩

/-- **Soundness of `N`.** If every entry passes `chkN`, every position in `N` is `≤ 0`. -/
theorem soundN {tn : Array Nat} (h : ∀ x ∈ tn, chkN tn (decode x) = true) {p : List Cell}
    (hm : mem tn p = true) : le (tf p) zero :=
  soundN_aux tn h _ p (Nat.lt_succ_self _) hm

theorem soundS_aux (ts tn : Array Nat) (hn : ∀ x ∈ tn, chkN tn (decode x) = true)
    (hs : ∀ x ∈ ts, chkS ts tn (decode x) = true) :
    ∀ n, ∀ p : List Cell, pot p < n → mem ts p = true → le (tf p) star
  | 0, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, p, hp, hm => by
    have hc := hs _ (mem_of_look hm)
    rw [decode_encode] at hc
    simp only [chkS, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true] at hc
    obtain ⟨⟨w, hw, hmw⟩, hl⟩ := hc
    refine le_star_of (fun q hq => ?_) ⟨w, hw, soundN hn hmw⟩
    rcases hl q hq with hq0 | ⟨r, hr, hmr⟩
    · exact not_star_le_of_le_zero (soundN hn hq0)
    · have h1 := pot_lt_of_mem_leftMoves hq
      have h2 := pot_lt_of_mem_rightMoves hr
      exact not_star_le_of_right ⟨r, hr, soundS_aux ts tn hn hs n r (by omega) hmr⟩

/-- **Soundness of `S`.** If every entry of `N` passes `chkN` and every entry of `S` passes
`chkS`, every position in `S` is `≤ ∗`. -/
theorem soundS {ts tn : Array Nat} (hn : ∀ x ∈ tn, chkN tn (decode x) = true)
    (hs : ∀ x ∈ ts, chkS ts tn (decode x) = true) {p : List Cell} (hm : mem ts p = true) :
    le (tf p) star :=
  soundS_aux ts tn hn hs _ p (Nat.lt_succ_self _) hm

/-- `G ≠ 0` (indeed `G ≰ 0` fails from Right's side: `0 ≤ G` is false) if some Right move is `≤ 0`. -/
theorem not_zero_le_of_right {p r : List Cell} (hr : r ∈ rightMoves p) (h : le (tf r) zero) :
    ¬ le zero (tf p) := fun h' =>
  not_right_le (mem_right_tf.2 ⟨r, hr, rfl⟩) (le_trans _ _ _ h h')

/-! ## Tables from text, and checks over index ranges -/

/-- The value of a digit of the base-64 text encoding (characters `#` to `[` and `]` to `c`,
avoiding the backslash). -/
def digitOf (c : Char) : Nat := if c.toNat < 92 then c.toNat - 35 else c.toNat - 36

/-- Parse the text of a table: the differences between consecutive codes (sorted ascending), each
written in base 32 with the most significant digit first; a digit value `v` carries `v % 32`, and
`v ≥ 32` means that more digits follow. The state is (codes so far, last code, current number). -/
def parseDeltas (st : Array Nat × Nat × Nat) (s : String) : Array Nat × Nat × Nat :=
  s.foldl (fun (st : Array Nat × Nat × Nat) c =>
    let v := digitOf c
    let cur := st.2.2 * 32 + v % 32
    if v < 32 then (st.1.push (st.2.1 + cur), st.2.1 + cur, 0) else (st.1, st.2.1, cur)) st

/-- A table from its text parts. -/
def ofParts (parts : List String) : Array Nat := (parts.foldl parseDeltas (#[], 0, 0)).1

/-- `P` holds for the entries `lo, …, hi - 1` of `t`. -/
def rangeAll (t : Array Nat) (P : Nat → Bool) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all fun i => P (t[i]?.getD 0)

theorem rangeAll_append {t : Array Nat} {P : Nat → Bool} {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : rangeAll t P a b = true) (h2 : rangeAll t P b c = true) : rangeAll t P a c = true := by
  unfold rangeAll at *
  have : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    have e := (List.range'_append (s := a) (m := b - a) (n := c - b) (step := 1)).symm
    rw [show a + 1 * (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at e
    exact e
  rw [this, List.all_append, h1, h2]; rfl

theorem forall_of_rangeAll {t : Array Nat} {P : Nat → Bool} (h : rangeAll t P 0 t.size = true) :
    ∀ x ∈ t, P x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  unfold rangeAll at h
  rw [List.all_eq_true] at h
  have := h i (by simp [List.mem_range']; omega)
  simpa [hi] using this

end Table
end Cgt
