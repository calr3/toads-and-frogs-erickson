import Cgt.Infinitesimal

/-!
# Toads and Frogs

The game is played on a `1 × n` strip. Left owns the toads `T`, which move rightwards,
Right owns the frogs `F`, which move leftwards:

* a toad may slide into an adjacent empty square on its right: `T□ → □T`;
* a toad may jump over a single frog immediately to its right, landing on the empty
  square just beyond: `TF□ → □FT`;
* a frog may slide into an adjacent empty square on its left: `□F → F□`;
* a frog may jump over a single toad immediately to its left, landing on the empty square
  just beyond: `□TF → FT□`.

`tf p` is the game value of the position `p`, and `start a b = Tᵃ □ᵇ Fᵃ`.
-/

namespace Cgt

/-- A square of the strip. -/
inductive Cell where
  | E  -- empty square `□`
  | T  -- toad (Left)
  | F  -- frog (Right)
  deriving DecidableEq, Repr

namespace Cell

/-- Swap toads and frogs. -/
def swap : Cell → Cell
  | E => E
  | T => F
  | F => T

@[simp] theorem swap_swap (c : Cell) : c.swap.swap = c := by cases c <;> rfl
@[simp] theorem swap_E : swap E = E := rfl
@[simp] theorem swap_T : swap T = F := rfl
@[simp] theorem swap_F : swap F = T := rfl

end Cell

open Cell

namespace TF

/-- All positions reachable by one Left (toad) move. -/
def leftMoves : List Cell → List (List Cell)
  | [] => []
  | c :: rest =>
    (match c, rest with
      | T, E :: r => [E :: T :: r]
      | T, F :: E :: r => [E :: F :: T :: r]
      | _, _ => []) ++ (leftMoves rest).map (c :: ·)

/-- All positions reachable by one Right (frog) move. -/
def rightMoves : List Cell → List (List Cell)
  | [] => []
  | c :: rest =>
    (match c, rest with
      | E, F :: r => [F :: E :: r]
      | E, T :: F :: r => [F :: T :: E :: r]
      | _, _ => []) ++ (rightMoves rest).map (c :: ·)

theorem mem_leftMoves {p q : List Cell} :
    q ∈ leftMoves p ↔
      (∃ u r, p = u ++ T :: E :: r ∧ q = u ++ E :: T :: r) ∨
      (∃ u r, p = u ++ T :: F :: E :: r ∧ q = u ++ E :: F :: T :: r) := by
  induction p generalizing q with
  | nil =>
    simp only [leftMoves, List.not_mem_nil, false_iff]
    rintro (⟨u, r, h, -⟩ | ⟨u, r, h, -⟩) <;> cases u <;> simp at h
  | cons c rest ih =>
    simp only [leftMoves, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨q', hq', rfl⟩)
      · match c, rest, h with
        | T, E :: r, h =>
          simp at h; subst h
          exact Or.inl ⟨[], r, rfl, rfl⟩
        | T, F :: E :: r, h =>
          simp at h; subst h
          exact Or.inr ⟨[], r, rfl, rfl⟩
      · rcases ih.1 hq' with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
        · exact Or.inl ⟨c :: u, r, rfl, rfl⟩
        · exact Or.inr ⟨c :: u, r, rfl, rfl⟩
    · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
      · cases u with
        | nil =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          left; simp
        | cons d u =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          right; exact ⟨u ++ E :: T :: r, ih.2 (Or.inl ⟨u, r, rfl, rfl⟩), rfl⟩
      · cases u with
        | nil =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          left; simp
        | cons d u =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          right; exact ⟨u ++ E :: F :: T :: r, ih.2 (Or.inr ⟨u, r, rfl, rfl⟩), rfl⟩

theorem mem_rightMoves {p q : List Cell} :
    q ∈ rightMoves p ↔
      (∃ u r, p = u ++ E :: F :: r ∧ q = u ++ F :: E :: r) ∨
      (∃ u r, p = u ++ E :: T :: F :: r ∧ q = u ++ F :: T :: E :: r) := by
  induction p generalizing q with
  | nil =>
    simp only [rightMoves, List.not_mem_nil, false_iff]
    rintro (⟨u, r, h, -⟩ | ⟨u, r, h, -⟩) <;> cases u <;> simp at h
  | cons c rest ih =>
    simp only [rightMoves, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨q', hq', rfl⟩)
      · match c, rest, h with
        | E, F :: r, h =>
          simp at h; subst h
          exact Or.inl ⟨[], r, rfl, rfl⟩
        | E, T :: F :: r, h =>
          simp at h; subst h
          exact Or.inr ⟨[], r, rfl, rfl⟩
      · rcases ih.1 hq' with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
        · exact Or.inl ⟨c :: u, r, rfl, rfl⟩
        · exact Or.inr ⟨c :: u, r, rfl, rfl⟩
    · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
      · cases u with
        | nil =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          left; simp
        | cons d u =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          right; exact ⟨u ++ F :: E :: r, ih.2 (Or.inl ⟨u, r, rfl, rfl⟩), rfl⟩
      · cases u with
        | nil =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          left; simp
        | cons d u =>
          simp at hp; obtain ⟨rfl, rfl⟩ := hp
          right; exact ⟨u ++ F :: T :: E :: r, ih.2 (Or.inr ⟨u, r, rfl, rfl⟩), rfl⟩

/-! ### Termination measure -/

/-- Number of toads in a list. -/
def countT : List Cell → Nat
  | [] => 0
  | c :: r => (if c = T then 1 else 0) + countT r

/-- Number of frogs in a list. -/
def countF : List Cell → Nat
  | [] => 0
  | c :: r => (if c = F then 1 else 0) + countF r

/-- Sum over toads of the number of squares to their right, plus the sum over frogs of
the number of squares to their left. Every move decreases it by exactly one. -/
def pot : List Cell → Nat
  | [] => 0
  | c :: r => (if c = T then r.length else 0) + countF r + pot r

theorem countF_append (u v : List Cell) : countF (u ++ v) = countF u + countF v := by
  induction u with
  | nil => simp [countF]
  | cons c u ih => simp [countF, ih]; omega

theorem pot_append (u v : List Cell) :
    pot (u ++ v) = pot u + pot v + countT u * v.length + countF v * u.length := by
  induction u with
  | nil => simp [pot, countT]
  | cons c u ih =>
    simp only [List.cons_append, pot, List.length_append, countF_append, ih, countT,
      List.length_cons]
    split <;> simp [Nat.add_mul, Nat.mul_add] <;> omega

theorem pot_lt_of_mem_leftMoves {p q : List Cell} (h : q ∈ leftMoves p) : pot q < pot p := by
  rcases mem_leftMoves.1 h with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
  · rw [pot_append, pot_append]
    simp [pot, countT, countF]
    try omega
  · rw [pot_append, pot_append]
    simp [pot, countT, countF]
    try omega

theorem pot_lt_of_mem_rightMoves {p q : List Cell} (h : q ∈ rightMoves p) :
    pot q < pot p := by
  rcases mem_rightMoves.1 h with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
  · rw [pot_append, pot_append]
    simp [pot, countT, countF]
    try omega
  · rw [pot_append, pot_append]
    simp [pot, countT, countF]
    try omega

end TF

open TF

/-- The game value of a Toads and Frogs position. -/
def tf (p : List Cell) : Game :=
  Game.mk ((leftMoves p).attach.map fun q => tf q.1) ((rightMoves p).attach.map fun q => tf q.1)
termination_by pot p
decreasing_by
  · exact pot_lt_of_mem_leftMoves q.2
  · exact pot_lt_of_mem_rightMoves q.2

/-- The starting position `Tᵃ □ᵇ Fᵃ`. -/
def start (a b : Nat) : List Cell := List.replicate a T ++ List.replicate b E ++ List.replicate a F

end Cgt

namespace Cgt
open Cell TF

theorem mem_left_tf {p : List Cell} {x : Game} :
    x ∈ (tf p).left ↔ ∃ q ∈ leftMoves p, x = tf q := by
  rw [tf]
  simp only [Game.left_mk, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

theorem mem_right_tf {p : List Cell} {x : Game} :
    x ∈ (tf p).right ↔ ∃ q ∈ rightMoves p, x = tf q := by
  rw [tf]
  simp only [Game.right_mk, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

/-! ### Mirror symmetry -/

/-- Reverse the strip and swap toads with frogs. -/
def mirror (p : List Cell) : List Cell := (p.map Cell.swap).reverse

@[simp] theorem mirror_append (u v : List Cell) : mirror (u ++ v) = mirror v ++ mirror u := by
  simp [mirror]

@[simp] theorem mirror_cons (c : Cell) (u : List Cell) :
    mirror (c :: u) = mirror u ++ [c.swap] := by
  simp [mirror]

@[simp] theorem mirror_nil : mirror [] = [] := rfl

@[simp] theorem mirror_mirror (p : List Cell) : mirror (mirror p) = p := by
  simp [mirror, List.map_reverse, List.map_map, Function.comp_def]

theorem mirror_injective {p q : List Cell} (h : mirror p = mirror q) : p = q := by
  rw [← mirror_mirror p, h, mirror_mirror]

theorem mem_leftMoves_mirror {p q : List Cell} :
    q ∈ leftMoves (mirror p) ↔ ∃ q' ∈ rightMoves p, q = mirror q' := by
  rw [mem_leftMoves]
  constructor
  · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
    · have hp' : p = mirror r ++ E :: F :: mirror u := by
        rw [← mirror_mirror p, hp]; simp
      refine ⟨mirror r ++ F :: E :: mirror u, mem_rightMoves.2 (Or.inl ⟨_, _, hp', rfl⟩), ?_⟩
      simp
    · have hp' : p = mirror r ++ E :: T :: F :: mirror u := by
        rw [← mirror_mirror p, hp]; simp
      refine ⟨mirror r ++ F :: T :: E :: mirror u,
        mem_rightMoves.2 (Or.inr ⟨_, _, hp', rfl⟩), ?_⟩
      simp
  · rintro ⟨q', hq', rfl⟩
    rcases mem_rightMoves.1 hq' with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
    · exact Or.inl ⟨mirror r, mirror u, by simp, by simp⟩
    · exact Or.inr ⟨mirror r, mirror u, by simp, by simp⟩

theorem mem_rightMoves_mirror {p q : List Cell} :
    q ∈ rightMoves (mirror p) ↔ ∃ q' ∈ leftMoves p, q = mirror q' := by
  rw [mem_rightMoves]
  constructor
  · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
    · have hp' : p = mirror r ++ T :: E :: mirror u := by
        rw [← mirror_mirror p, hp]; simp
      refine ⟨mirror r ++ E :: T :: mirror u, mem_leftMoves.2 (Or.inl ⟨_, _, hp', rfl⟩), ?_⟩
      simp
    · have hp' : p = mirror r ++ T :: F :: E :: mirror u := by
        rw [← mirror_mirror p, hp]; simp
      refine ⟨mirror r ++ E :: F :: T :: mirror u,
        mem_leftMoves.2 (Or.inr ⟨_, _, hp', rfl⟩), ?_⟩
      simp
  · rintro ⟨q', hq', rfl⟩
    rcases mem_leftMoves.1 hq' with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
    · exact Or.inl ⟨mirror r, mirror u, by simp, by simp⟩
    · exact Or.inr ⟨mirror r, mirror u, by simp, by simp⟩

/-- The mirror image of a position is its negative. -/
theorem tf_mirror (p : List Cell) : Game.Equiv (tf (mirror p)) (Game.neg (tf p)) := by
  induction hn : pot p using Nat.strongRecOn generalizing p with
  | _ n ih =>
  have hneg := Game.neg_mk (tf p).left (tf p).right
  have htp : tf p = Game.mk (tf p).left (tf p).right := by cases h : tf p; rfl
  rw [← htp] at hneg
  rw [hneg]
  have htm : tf (mirror p) = Game.mk (tf (mirror p)).left (tf (mirror p)).right := by
    cases h : tf (mirror p); rfl
  rw [htm]
  apply Game.equiv_of_options
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
    obtain ⟨q', hq', rfl⟩ := mem_leftMoves_mirror.1 hq
    refine ⟨Game.neg (tf q'), ?_, ih _ (by have := pot_lt_of_mem_rightMoves hq'; omega) q' rfl⟩
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨tf q', mem_right_tf.2 ⟨q', hq', rfl⟩, rfl⟩
  · intro x' hx'
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    obtain ⟨q', hq', rfl⟩ := mem_right_tf.1 hy
    refine ⟨tf (mirror q'), mem_left_tf.2 ⟨mirror q', mem_leftMoves_mirror.2 ⟨q', hq', rfl⟩, rfl⟩,
      (ih _ (by have := pot_lt_of_mem_rightMoves hq'; omega) q' rfl).symm⟩
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_right_tf.1 hx
    obtain ⟨q', hq', rfl⟩ := mem_rightMoves_mirror.1 hq
    refine ⟨Game.neg (tf q'), ?_, ih _ (by have := pot_lt_of_mem_leftMoves hq'; omega) q' rfl⟩
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨tf q', mem_left_tf.2 ⟨q', hq', rfl⟩, rfl⟩
  · intro x' hx'
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    obtain ⟨q', hq', rfl⟩ := mem_left_tf.1 hy
    refine ⟨tf (mirror q'),
      mem_right_tf.2 ⟨mirror q', mem_rightMoves_mirror.2 ⟨q', hq', rfl⟩, rfl⟩,
      (ih _ (by have := pot_lt_of_mem_leftMoves hq'; omega) q' rfl).symm⟩

theorem mirror_start (a b : Nat) : mirror (start a b) = start a b := by
  simp [start, mirror, List.map_replicate, List.reverse_replicate, List.append_assoc]

/-- For a mirror-symmetric position, being infinitesimal is equivalent to having Left stop
at most `0`. -/
theorem infinitesimal_iff_upperZero_of_symm {p : List Cell} (hp : mirror p = p) :
    Game.Infinitesimal (tf p) ↔ Game.UpperZero (tf p) := by
  constructor
  · exact Game.upperZero_of_infinitesimal
  · intro h
    have e := tf_mirror p
    rw [hp] at e
    exact Game.infinitesimal_of_upperZero h e.symm

theorem infinitesimal_start_iff (a b : Nat) :
    Game.Infinitesimal (tf (start a b)) ↔ Game.UpperZero (tf (start a b)) :=
  infinitesimal_iff_upperZero_of_symm (mirror_start a b)

end Cgt
