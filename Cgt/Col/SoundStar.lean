import Cgt.Col.Sound
import Cgt.RowA2Values

/-!
# Soundness of the finite check for `≤ ∗`

The column analogue of the exact values of the row `a = 2` (`Cgt/RowA2Values.lean`): a position is
`≤ ∗` if some Right move reaches a position `≤ 0` (this answers Left taking the `∗`), and every
Left move reaches a position that is `≤ 0` or has a Right reply `≤ ∗` (`le_star_of`).

`chkS` checks this for the witnesses of the keys of a tree `tS`, with normal-play keys in `tN`.
`soundS` lifts it to every run list with a key in `tS`, by the same induction on `pot` and the same
margin lemmas as `sound`. A symmetric position that is `≤ ∗` is `∗` (`equiv_star_of_mirror`).
-/

namespace Cgt
namespace Col
open Cell TF Game

/-- The check of a witness `W` of a `≤ ∗` key: some Right move has a key in `tN`, and every Left
move has a key in `tN` or a Right reply with a key in `tS`. -/
def chkS (r : GapRule) (tS tN : LTree) (W : RL) : Bool :=
  (rmovesR W).any (fun Z => tN.mem (keyOf r Z)) &&
    (lmovesR W).all fun X => tN.mem (keyOf r X) || (rmovesR X).any fun Z => tS.mem (keyOf r Z)

/-- The normal-play half of `sound`, on its own. -/
theorem soundN {r : GapRule} (hm : Margin r) (tN : LTree)
    (hcN : ∀ k ∈ tN.toList, ∀ W ∈ witOf r k, chkN r tN W = true) {R : RL} (hR : maxB R = true)
    (hk : tN.mem (keyOf r R) = true) : le (tf (expand R)) zero :=
  (sound hm LTree.leaf tN (fun k hk => by simp [LTree.toList] at hk) hcN _ R hR (Nat.lt_succ_self _)).1 hk

/-- **Soundness for `≤ ∗`.** If the check passes, every maximal run list with a key in `tS` is
`≤ ∗`. -/
theorem soundS {r : GapRule} (hm : Margin r) (tS tN : LTree)
    (hcS : ∀ k ∈ tS.toList, ∀ W ∈ witOf r k, chkS r tS tN W = true)
    (hcN : ∀ k ∈ tN.toList, ∀ W ∈ witOf r k, chkN r tN W = true) :
    ∀ (n : Nat) (R : RL), maxB R = true → pot (expand R) < n →
      tS.mem (keyOf r R) = true → le (tf (expand R)) star := by
  intro n
  induction n with
  | zero => intro R _ h; omega
  | succ n ih =>
    intro R hR hpot hk
    have hpos := posR_of_maxB hR
    obtain ⟨W, hW, hRW, hWm⟩ := hm.wit R hR
    have hchk := hcS _ (LTree.mem_toList hk) W hW
    unfold chkS at hchk
    rw [Bool.and_eq_true] at hchk
    obtain ⟨hright, hmoves⟩ := hchk
    apply le_star_of
    · -- every Left move: `≤ 0`, or a Right reply `≤ ∗`
      intro q hq
      obtain ⟨X, hX, rfl⟩ := (mem_leftMoves_expand hpos).1 hq
      obtain ⟨X', hX', hXX⟩ := hm.left 2 R W X hRW hR hWm hX
      have hXm := maxB_of_mem_lmovesR hR hX
      have hXm' := maxB_of_mem_lmovesR hWm hX'
      have h2 := pot_lmovesR hR hX
      have hlf := List.all_eq_true.1 hmoves X' hX'
      rcases Bool.or_eq_true_iff.1 hlf with h | h
      · apply not_star_le_of_le_zero
        apply soundN hm tN hcN hXm
        rw [keyOf_eq_of_rel (hXX.mono' (by omega))]; exact h
      · obtain ⟨Z', hZ', hk'⟩ := List.any_eq_true.1 h
        obtain ⟨Z, hZ, hZZ⟩ := hm.right 0 X' X Z' hXX.symm hXm' hXm hZ'
        have hkey : keyOf r Z = keyOf r Z' := (keyOf_eq_of_rel hZZ).symm
        have hZm := maxB_of_mem_rmovesR hXm hZ
        have h1 := pot_rmovesR hXm hZ
        apply not_star_le_of_right
        exact ⟨expand Z, (mem_rightMoves_expand (posR_of_maxB hXm)).2 ⟨Z, hZ, rfl⟩,
          ih Z hZm (by omega) (by rw [hkey]; exact hk')⟩
    · -- Left takes the `∗`: a Right move to a position `≤ 0`
      obtain ⟨Z', hZ', hk'⟩ := List.any_eq_true.1 hright
      obtain ⟨Z, hZ, hZZ⟩ := hm.right 2 W R Z' hRW.symm hWm hR hZ'
      have hkey : keyOf r Z = keyOf r Z' := (keyOf_eq_of_rel (hZZ.mono' (by omega))).symm
      have hZm := maxB_of_mem_rmovesR hR hZ
      exact ⟨expand Z, (mem_rightMoves_expand hpos).2 ⟨Z, hZ, rfl⟩,
        soundN hm tN hcN hZm (by rw [hkey]; exact hk')⟩

end Col
end Cgt
