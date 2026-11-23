import Cgt.Sum.Gen.T3

/-!
# Three empty squares: `Tᵃ □³ Fᵇ = {a - b | a - b}` for `a, b ≥ 4`

Thanatipanonda's theorem (thesis, Theorem 5.6.1; *Three Results of Combinatorial Game Toads and
Frogs*, Section 3). The inequality `≤` is the generated proof plan of `Cgt/Sum/Gen/T3.lean`, in
four families (`a, b ≥ 5`; `a = 4`; `b = 4`; `a = b = 4`); `≥` follows by mirror symmetry.
-/

namespace Cgt

open Cell TF Game Col

/-- The position `Tᵃ □ᵏ Fᵇ`. -/
def unequal (a k b : Nat) : List Cell :=
  List.replicate a T ++ List.replicate k E ++ List.replicate b F

theorem mirror_unequal (a k b : Nat) : mirror (unequal a k b) = unequal b k a := by
  simp [unequal, mirror_append, mirror_replicate, List.append_assoc]

theorem three_le (a b : Nat) (ha : 4 ≤ a) (hb : 4 ≤ b) :
    le (tf (unequal a 3 b)) (starZ ((a : Int) - b)) := by
  have hE : ∀ a b, unequal a 3 b = expand [(T, a), (E, 3), (F, b)] := by
    intro a b; simp [unequal, expand]
  rw [hE]
  rcases Nat.lt_or_ge a 5 with h | h
  · have : a = 4 := by omega
    subst this
    rcases Nat.lt_or_ge b 5 with h' | h'
    · have : b = 4 := by omega
      subst this
      exact VR_cast T3_c261 rfl (congrArg starZ (by omega))
    · obtain ⟨y, rfl⟩ : ∃ y, b = y + 5 := ⟨b - 5, by omega⟩
      exact VR_cast (T3_c160 y) rfl (congrArg starZ (by omega))
  · obtain ⟨x, rfl⟩ : ∃ x, a = x + 5 := ⟨a - 5, by omega⟩
    rcases Nat.lt_or_ge b 5 with h' | h'
    · have : b = 4 := by omega
      subst this
      exact VR_cast (T3_c224 x) rfl (congrArg starZ (by omega))
    · obtain ⟨y, rfl⟩ : ∃ y, b = y + 5 := ⟨b - 5, by omega⟩
      exact VR_cast (T3_c78 x y) rfl (congrArg starZ (by omega))

/-- **`Tᵃ □³ Fᵇ = {a - b | a - b}` for `a, b ≥ 4`.** -/
theorem three_empty_value (a b : Nat) (ha : 4 ≤ a) (hb : 4 ≤ b) :
    Equiv (tf (unequal a 3 b)) (starZ ((a : Int) - b)) := by
  refine ⟨three_le a b ha hb, ?_⟩
  have h := three_le b a hb ha
  have hm := tf_mirror (unequal b 3 a)
  rw [mirror_unequal] at hm
  -- tf (unequal a 3 b) ≈ -(tf (unequal b 3 a)) ≥ -{b - a | b - a} = {a - b | a - b}
  have h2 : le (neg (starZ ((b : Int) - a))) (neg (tf (unequal b 3 a))) :=
    (neg_le_neg_iff _ _).2 h
  rw [neg_starZ] at h2
  have h3 : -((b : Int) - a) = (a : Int) - b := by omega
  rw [h3] at h2
  exact le_trans _ _ _ h2 hm.2

end Cgt
