import Cgt.Game

/-!
# Infinitesimals

We define the numbers `2⁻ⁿ` (`powHalf n`), the predicate `Infinitesimal`, and prove a
purely combinatorial characterisation of "`G ≤ 2⁻ⁿ` for every `n`" (i.e. the Left stop of
`G` is at most `0`):

* `UpperZero G :↔ ∀ n, G ≤ 2⁻ⁿ`  (Left stop `≤ 0`)
* `LfZero G :↔ ∀ n, ¬ 2⁻ⁿ ≤ G`   (Right stop `≤ 0`)

with
* `upperZero_iff : UpperZero G ↔ LfZero G ∧ ∀ Gᴸ, LfZero Gᴸ`
* `lfZero_iff : LfZero G ↔ G ≤ 0 ∨ ∃ Gᴿ, UpperZero Gᴿ`.
-/

namespace Cgt
namespace Game

/-- The dyadic number `2⁻ⁿ`: `powHalf 0 = 1 = {0 | }` and `powHalf (n+1) = {0 | powHalf n}`. -/
def powHalf : Nat → Game
  | 0 => mk [zero] []
  | n + 1 => mk [zero] [powHalf n]

@[simp] theorem powHalf_left (n : Nat) : (powHalf n).left = [zero] := by cases n <;> rfl
@[simp] theorem powHalf_right_zero : (powHalf 0).right = [] := rfl
@[simp] theorem powHalf_right_succ (n : Nat) : (powHalf (n + 1)).right = [powHalf n] := rfl

theorem not_powHalf_le_zero (n : Nat) : ¬ le (powHalf n) zero := by
  intro h
  rw [le_iff] at h
  exact h.1 zero (by simp) (le_refl zero)

theorem zero_le_powHalf (n : Nat) : le zero (powHalf n) := by
  rw [le_iff]
  refine ⟨fun x hx => by simp [zero] at hx, fun y hy => ?_⟩
  cases n with
  | zero => simp at hy
  | succ m =>
    simp at hy
    subst hy
    exact not_powHalf_le_zero m

theorem zero_lt_powHalf (n : Nat) : lt zero (powHalf n) :=
  ⟨zero_le_powHalf n, not_powHalf_le_zero n⟩

theorem powHalf_succ_le (n : Nat) : le (powHalf (n + 1)) (powHalf n) := by
  induction n with
  | zero =>
    rw [le_iff]
    refine ⟨fun x hx => ?_, fun y hy => by simp at hy⟩
    simp at hx; subst hx
    exact not_powHalf_le_zero 0
  | succ m ih =>
    rw [le_iff]
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · simp at hx; subst hx
      exact not_powHalf_le_zero (m + 1)
    · simp at hy; subst hy
      intro h
      -- `powHalf m ≤ powHalf (m+2)` would force `¬ powHalf (m+1) ≤ powHalf m`.
      rw [le_iff] at h
      exact h.2 (powHalf (m + 1)) (by simp) ih

theorem powHalf_succ_lt (n : Nat) : lt (powHalf (n + 1)) (powHalf n) := by
  refine ⟨powHalf_succ_le n, fun h => ?_⟩
  rw [le_iff] at h
  exact h.2 (powHalf n) (by simp) (le_refl _)

theorem powHalf_le_of_le {m n : Nat} (h : m ≤ n) : le (powHalf n) (powHalf m) := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans _ _ _ (powHalf_succ_le _) ih

/-- `UpperZero G` : `G ≤ 2⁻ⁿ` for all `n` (equivalently, the Left stop of `G` is `≤ 0`). -/
def UpperZero (g : Game) : Prop := ∀ n, le g (powHalf n)

/-- `LfZero G` : `2⁻ⁿ ≰ G` for all `n` (equivalently, the Right stop of `G` is `≤ 0`). -/
def LfZero (g : Game) : Prop := ∀ n, ¬ le (powHalf n) g

theorem upperZero_iff (g : Game) : UpperZero g ↔ LfZero g ∧ ∀ x ∈ g.left, LfZero x := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, fun x hx n hn => ?_⟩
    · have := h (n + 1)
      rw [le_iff] at this
      exact this.2 (powHalf n) (by simp) hn
    · have := h n
      rw [le_iff] at this
      exact this.1 x hx hn
  · rintro ⟨h1, h2⟩ n
    rw [le_iff]
    refine ⟨fun x hx => h2 x hx n, fun y hy => ?_⟩
    cases n with
    | zero => simp at hy
    | succ m =>
      simp at hy; subst hy
      exact h1 m

/-- If `y ≰ 2⁻ⁿ` then `y ≰ 2⁻ᴺ` for every `N ≥ n`. -/
theorem not_le_powHalf_mono {y : Game} {n N : Nat} (hn : n ≤ N) (h : ¬ le y (powHalf n)) :
    ¬ le y (powHalf N) :=
  fun h' => h (le_trans _ _ _ h' (powHalf_le_of_le hn))

theorem exists_common_bound (l : List Game) (h : ∀ y ∈ l, ∃ n, ¬ le y (powHalf n)) :
    ∃ N, ∀ y ∈ l, ¬ le y (powHalf N) := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons y l ih =>
    obtain ⟨n, hn⟩ := h y (by simp)
    obtain ⟨N, hN⟩ := ih (fun z hz => h z (by simp [hz]))
    refine ⟨max n N, fun z hz => ?_⟩
    simp at hz
    rcases hz with rfl | hz
    · exact not_le_powHalf_mono (Nat.le_max_left _ _) hn
    · exact not_le_powHalf_mono (Nat.le_max_right _ _) (hN z hz)

theorem lfZero_iff (g : Game) : LfZero g ↔ le g zero ∨ ∃ y ∈ g.right, UpperZero y := by
  have key : ∀ n, ¬ le (powHalf n) g ↔ le g zero ∨ ∃ y ∈ g.right, le y (powHalf n) := by
    intro n
    rw [le_iff]
    simp only [powHalf_left, List.mem_singleton, forall_eq]
    constructor
    · intro h
      by_cases hz : le g zero
      · exact Or.inl hz
      · right
        apply Classical.byContradiction
        intro hne
        apply h
        refine ⟨hz, fun y hy hle => hne ⟨y, hy, hle⟩⟩
    · rintro (hz | ⟨y, hy, hle⟩) ⟨h1, h2⟩
      · exact h1 hz
      · exact h2 y hy hle
  constructor
  · intro h
    by_cases hz : le g zero
    · exact Or.inl hz
    · right
      apply Classical.byContradiction
      intro hne
      have : ∀ y ∈ g.right, ∃ n, ¬ le y (powHalf n) := by
        intro y hy
        apply Classical.byContradiction
        intro hall
        exact hne ⟨y, hy, fun n => Classical.byContradiction fun hn => hall ⟨n, hn⟩⟩
      obtain ⟨N, hN⟩ := exists_common_bound _ this
      rcases (key N).1 (h N) with hz' | ⟨y, hy, hle⟩
      · exact hz hz'
      · exact hN y hy hle
  · rintro h n
    apply (key n).2
    rcases h with hz | ⟨y, hy, hu⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y, hy, hu n⟩

/-- A game is *infinitesimal* if it lies strictly between `-2⁻ⁿ` and `2⁻ⁿ` for every `n`,
equivalently strictly between `-x` and `x` for every positive (short) number `x`. -/
def Infinitesimal (g : Game) : Prop := ∀ n, lt (neg (powHalf n)) g ∧ lt g (powHalf n)

theorem lt_powHalf_of_upperZero {g : Game} (h : UpperZero g) (n : Nat) : lt g (powHalf n) :=
  lt_of_le_of_lt (h (n + 1)) (powHalf_succ_lt n)

theorem neg_lt_neg_iff (g h : Game) : lt (neg g) (neg h) ↔ lt h g := by
  unfold lt
  rw [neg_le_neg_iff, neg_le_neg_iff]

/-- A game equivalent to its own negative whose Left stop is `≤ 0` is infinitesimal. -/
theorem infinitesimal_of_upperZero {g : Game} (h : UpperZero g) (hs : Equiv (neg g) g) :
    Infinitesimal g := by
  intro n
  refine ⟨?_, lt_powHalf_of_upperZero h n⟩
  have h1 : lt (neg (powHalf n)) (neg g) := (neg_lt_neg_iff _ _).2 (lt_powHalf_of_upperZero h n)
  exact lt_of_lt_of_le h1 hs.1

/-- Conversely, an infinitesimal game has Left stop `≤ 0`. -/
theorem upperZero_of_infinitesimal {g : Game} (h : Infinitesimal g) : UpperZero g :=
  fun n => (h n).2.1

end Game
end Cgt

namespace Cgt
namespace Game

theorem neg_zero : neg zero = zero := by
  rw [zero, neg_mk]; rfl

/-- A game equivalent to its own negative always has Right stop `≥ 0`... more precisely it
satisfies `LfZero` (its Right stop is `≤ 0`). -/
theorem lfZero_of_equiv_neg {g : Game} (hs : Equiv (neg g) g) : LfZero g := by
  intro n h
  have h1 : le (neg g) (neg (powHalf n)) := (neg_le_neg_iff _ _).2 h
  have h2 : le (powHalf n) (neg (powHalf n)) := le_trans _ _ _ h (le_trans _ _ _ hs.2 h1)
  have h3 : le (neg (powHalf n)) zero := by
    have := (neg_le_neg_iff (powHalf n) zero).2 (zero_le_powHalf n)
    rwa [neg_zero] at this
  exact not_powHalf_le_zero n (le_trans _ _ _ h2 h3)

end Game
end Cgt
