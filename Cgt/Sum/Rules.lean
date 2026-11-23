import Cgt.Col.Runs
import Cgt.Sum.ZNum
import Cgt.Sum.Block

/-!
# Comparison rules for positions given as run lists

`VR R` is the value of the position `expand R`. The rules of `Cgt/Sum/ZNum.lean` for comparing
with an integer `n` (of either sign) and with `{n | n}` are restated with the explicit move lists
`lmovesR`, `rmovesR` of `Cgt/Col/Runs.lean`, which `simp` can compute for run lists with symbolic
lengths.
-/

namespace Cgt
namespace Col

open Cell TF Game

/-- The value of the position with run list `R`. -/
def VR (R : RL) : Game := tf (expand R)

theorem mem_left_VR {R : RL} (hR : maxB R = true) {x : Game} :
    x ∈ (VR R).left ↔ ∃ X ∈ lmovesR R, x = VR X := by
  unfold VR
  rw [mem_left_tf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨X, hX, rfl⟩ := (mem_leftMoves_expand (posR_of_maxB hR)).1 hq
    exact ⟨X, hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨_, (mem_leftMoves_expand (posR_of_maxB hR)).2 ⟨X, hX, rfl⟩, rfl⟩

theorem mem_right_VR {R : RL} (hR : maxB R = true) {y : Game} :
    y ∈ (VR R).right ↔ ∃ Y ∈ rmovesR R, y = VR Y := by
  unfold VR
  rw [mem_right_tf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨Y, hY, rfl⟩ := (mem_rightMoves_expand (posR_of_maxB hR)).1 hq
    exact ⟨Y, hY, rfl⟩
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨_, (mem_rightMoves_expand (posR_of_maxB hR)).2 ⟨Y, hY, rfl⟩, rfl⟩

/-- `VR R ≤ n`: every Left move costs Left a move (`≤ n - 1`) or is answered by a Right move back
to `≤ n`; and for negative `n` Right has a move to `≤ n + 1`. -/
theorem VR_le_zint {R : RL} {n : Int} (hR : maxB R = true)
    (h1 : ∀ X ∈ lmovesR R, le (VR X) (zint (n - 1)) ∨ ∃ Y ∈ rmovesR X, le (VR Y) (zint n))
    (h2 : n < 0 → ∃ Y ∈ rmovesR R, le (VR Y) (zint (n + 1))) : le (VR R) (zint n) := by
  apply le_zint_of
  · intro x hx
    obtain ⟨X, hX, rfl⟩ := (mem_left_VR hR).1 hx
    rcases h1 X hX with h | ⟨Y, hY, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, (mem_right_VR (maxB_of_mem_lmovesR hR hX)).2 ⟨Y, hY, rfl⟩, h⟩
  · intro hn
    obtain ⟨Y, hY, h⟩ := h2 hn
    exact ⟨_, (mem_right_VR hR).2 ⟨Y, hY, rfl⟩, h⟩

/-- `VR R ≤ {n | n}`: every Left move leads to `≤ n` or is answered by a Right move back to
`≤ {n | n}`; and Right has a move to `≤ n`. -/
theorem VR_le_starZ {R : RL} {n : Int} (hR : maxB R = true)
    (h1 : ∀ X ∈ lmovesR R, le (VR X) (zint n) ∨ ∃ Y ∈ rmovesR X, le (VR Y) (starZ n))
    (h2 : ∃ Y ∈ rmovesR R, le (VR Y) (zint n)) : le (VR R) (starZ n) := by
  apply le_star_of
  · intro x hx
    obtain ⟨X, hX, rfl⟩ := (mem_left_VR hR).1 hx
    rcases h1 X hX with h | ⟨Y, hY, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, (mem_right_VR (maxB_of_mem_lmovesR hR hX)).2 ⟨Y, hY, rfl⟩, h⟩
  · obtain ⟨Y, hY, h⟩ := h2
    exact ⟨_, (mem_right_VR hR).2 ⟨Y, hY, rfl⟩, h⟩

theorem VR_le_zint_mono {R : RL} {m n : Int} (h : le (VR R) (zint m)) (hmn : m ≤ n) :
    le (VR R) (zint n) :=
  le_trans _ _ _ h (zint_le_zint hmn)

/-- Transport a bound along equalities of the run list and of the bound. -/
theorem VR_cast {R R' : RL} {g g' : Game} (h : le (VR R') g') (hR : R = R') (hg : g = g') :
    le (VR R) g := by
  subst hR; subst hg; exact h

/-- The Blocking Rule for a run list that splits as `X FF Y`. -/
theorem VR_split {R RX RY : RL} {m m' n : Int} (h : expand R = expand RX ++ F :: F :: expand RY)
    (hX : le (VR RX) (zint m)) (hY : le (VR RY) (zint m')) (hn : m + m' ≤ n) :
    le (VR R) (zint n) := by
  unfold VR
  rw [h]
  exact le_trans _ _ _ (blocking_rule _ _ m m' hX hY) (zint_le_zint hn)

end Col
end Cgt
