import Cgt.Col.Rel

/-!
# Soundness of the finite check

If `checkCol tU tN` holds, then every maximal run list whose key is in `tN` is `≤ 0`, and every one
whose key is in `tU` has Left stop `≤ 0` (`UpperZero`). The proof is an induction on `pot`, as for
the row `a = 2`. It uses three properties of the margin relation, collected in `Margin`:

* every run list has a witness of its key within margin 4;
* Left moves and Right moves of related run lists correspond, losing 2 of the margin.
-/

namespace Cgt
namespace Col
open Cell TF Game

/-- What the soundness proof needs from `Rel`. -/
structure Margin (r : GapRule) : Prop where
  wit : ∀ R : RL, maxB R = true → ∃ W ∈ witOf r (keyOf r R), Rel r 4 R W ∧ maxB W = true
  left : ∀ (j : Nat) (R R' X : RL), Rel r (j + 2) R R' → maxB R = true → maxB R' = true →
    X ∈ lmovesR R → ∃ X' ∈ lmovesR R', Rel r j X X'
  right : ∀ (j : Nat) (R R' Y : RL), Rel r (j + 2) R R' → maxB R = true → maxB R' = true →
    Y ∈ rmovesR R → ∃ Y' ∈ rmovesR R', Rel r j Y Y'

theorem pot_lmovesR {R X : RL} (hR : maxB R = true) (hX : X ∈ lmovesR R) : pot (expand X) < pot (expand R) :=
  pot_lt_of_mem_leftMoves ((mem_leftMoves_expand (posR_of_maxB hR)).2 ⟨X, hX, rfl⟩)

theorem pot_rmovesR {R Y : RL} (hR : maxB R = true) (hY : Y ∈ rmovesR R) : pot (expand Y) < pot (expand R) :=
  pot_lt_of_mem_rightMoves ((mem_rightMoves_expand (posR_of_maxB hR)).2 ⟨Y, hY, rfl⟩)

/-- A check of a list, split into chunks of `n`. -/
theorem all_of_chunks {α : Type} (p : α → Bool) (n : Nat) :
    ∀ (k : Nat) (l : List α), l.length ≤ n * k → (∀ i, i < k → ((l.drop (n * i)).take n).all p = true) →
      l.all p = true
  | 0, l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | k + 1, l, hl, h => by
    rw [← List.take_append_drop n l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks p n k (l.drop n) (by simp; rw [Nat.mul_succ] at hl; omega)
      (fun i hi => ?_)⟩
    have := h (i + 1) (by omega)
    rwa [List.drop_drop, show n + n * i = n * (i + 1) by rw [Nat.mul_succ]; omega]

/-- A check of a list, split into consecutive chunks of the given sizes. -/
theorem all_of_sizes {α : Type} (p : α → Bool) :
    ∀ (cs : List Nat) (l : List α), l.length ≤ cs.sum →
      (∀ i, i < cs.length → ((l.drop (cs.take i).sum).take (cs.getD i 0)).all p = true) → l.all p = true
  | [], l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; rfl
  | c :: cs, l, hl, h => by
    rw [← List.take_append_drop c l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), all_of_sizes p cs (l.drop c) (by simp at hl ⊢; omega)
      (fun i hi => ?_)⟩
    have := h (i + 1) (by simp; omega)
    simpa [List.drop_drop, List.take_succ_cons, List.sum_cons] using this

theorem sound {r : GapRule} (hm : Margin r) (tU tN : LTree)
    (hcU : ∀ k ∈ tU.toList, ∀ W ∈ witOf r k, chkU r tU tN W = true)
    (hcN : ∀ k ∈ tN.toList, ∀ W ∈ witOf r k, chkN r tN W = true) :
    ∀ (n : Nat) (R : RL), maxB R = true → pot (expand R) < n →
      (tN.mem (keyOf r R) = true → le (tf (expand R)) zero) ∧
      (tU.mem (keyOf r R) = true → UpperZero (tf (expand R))) := by
  intro n
  induction n with
  | zero => intro R _ h; omega
  | succ n ih =>
    intro R hR hpot
    have hpos := posR_of_maxB hR
    -- the normal-play claim
    have hN : tN.mem (keyOf r R) = true → le (tf (expand R)) zero := by
      intro hk
      obtain ⟨W, hW, hRW, hWm⟩ := hm.wit R hR
      have hchk := hcN _ (LTree.mem_toList hk) W hW
      unfold chkN at hchk
      rw [List.all_eq_true] at hchk
      rw [le_zero_iff_tf]
      intro q hq
      obtain ⟨X, hX, rfl⟩ := (mem_leftMoves_expand hpos).1 hq
      obtain ⟨X', hX', hXX⟩ := hm.left 2 R W X hRW hR hWm hX
      have hXm := maxB_of_mem_lmovesR hR hX
      have hXm' := maxB_of_mem_lmovesR hWm hX'
      obtain ⟨Z', hZ', hk'⟩ := List.any_eq_true.1 (hchk X' hX')
      obtain ⟨Z, hZ, hZZ⟩ := hm.right 0 X' X Z' hXX.symm hXm' hXm hZ'
      have hkey : keyOf r Z = keyOf r Z' := (keyOf_eq_of_rel hZZ).symm
      have hZm := maxB_of_mem_rmovesR hXm hZ
      refine ⟨expand Z, (mem_rightMoves_expand (posR_of_maxB hXm)).2 ⟨Z, hZ, rfl⟩, ?_⟩
      have h1 := pot_rmovesR hXm hZ
      have h2 := pot_lmovesR hR hX
      exact (ih Z hZm (by omega)).1 (by rw [hkey]; exact hk')
    refine ⟨hN, fun hk => ?_⟩
    -- the Left-stop claim
    obtain ⟨W, hW, hRW, hWm⟩ := hm.wit R hR
    have hchk := hcU _ (LTree.mem_toList hk) W hW
    unfold chkU at hchk
    simp only [Bool.and_eq_true, List.all_eq_true] at hchk
    obtain ⟨hpass, hmoves⟩ := hchk
    rw [upperZero_tf_iff]
    constructor
    · -- Left passes
      rw [lfZero_tf_iff]
      unfold lfOK at hpass
      rcases Bool.or_eq_true_iff.1 hpass with h | h
      · left
        apply hN
        rw [keyOf_eq_of_rel (hRW.mono' (by omega))]; exact h
      · right
        obtain ⟨Z', hZ', hk'⟩ := List.any_eq_true.1 h
        obtain ⟨Z, hZ, hZZ⟩ := hm.right 2 W R Z' hRW.symm hWm hR hZ'
        have hkey : keyOf r Z = keyOf r Z' := (keyOf_eq_of_rel (hZZ.mono' (by omega))).symm
        have hZm := maxB_of_mem_rmovesR hR hZ
        refine ⟨expand Z, (mem_rightMoves_expand hpos).2 ⟨Z, hZ, rfl⟩, ?_⟩
        have h1 := pot_rmovesR hR hZ
        exact (ih Z hZm (by omega)).2 (by rw [hkey]; exact hk')
    · -- Left moves
      intro q hq
      obtain ⟨X, hX, rfl⟩ := (mem_leftMoves_expand hpos).1 hq
      obtain ⟨X', hX', hXX⟩ := hm.left 2 R W X hRW hR hWm hX
      have hXm := maxB_of_mem_lmovesR hR hX
      have hXm' := maxB_of_mem_lmovesR hWm hX'
      have h2 := pot_lmovesR hR hX
      have hlf := hmoves X' hX'
      rw [lfZero_tf_iff]
      unfold lfOK at hlf
      rcases Bool.or_eq_true_iff.1 hlf with h | h
      · left
        refine (ih X hXm (by omega)).1 ?_
        rw [keyOf_eq_of_rel (hXX.mono' (by omega))]; exact h
      · right
        obtain ⟨Z', hZ', hk'⟩ := List.any_eq_true.1 h
        obtain ⟨Z, hZ, hZZ⟩ := hm.right 0 X' X Z' hXX.symm hXm' hXm hZ'
        have hkey : keyOf r Z = keyOf r Z' := (keyOf_eq_of_rel hZZ).symm
        have hZm := maxB_of_mem_rmovesR hXm hZ
        refine ⟨expand Z, (mem_rightMoves_expand (posR_of_maxB hXm)).2 ⟨Z, hZ, rfl⟩, ?_⟩
        have h1 := pot_rmovesR hXm hZ
        exact (ih Z hZm (by omega)).2 (by rw [hkey]; exact hk')

end Col
end Cgt
