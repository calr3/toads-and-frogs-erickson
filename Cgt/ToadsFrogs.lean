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
