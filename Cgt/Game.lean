/-!
# Short partizan games

A minimal, self-contained development of short combinatorial games (Conway games
with finitely many options), with exactly what is needed to state and prove
infinitesimality results:

* `Game` – games given by finite lists of Left and Right options;
* `Game.le` – Conway's order `G ≤ H`, and `Game.lt`;
* `Game.neg` – negation;
* `Game.powHalf n` – the number `2⁻ⁿ`;
* `Game.Infinitesimal` – `G` lies strictly between `-2⁻ⁿ` and `2⁻ⁿ` for every `n`.

Since every positive (short) number is at least `2⁻ⁿ` for some `n`, the predicate
`Infinitesimal` is the usual notion "`-x < G < x` for every positive number `x`".
-/

namespace Cgt

/-- A short game, given by its finite lists of Left and Right options. -/
inductive Game where
  | mk : List Game → List Game → Game

namespace Game

instance : Inhabited Game := ⟨mk [] []⟩

/-- The Left options of a game. -/
def left : Game → List Game
  | mk l _ => l

/-- The Right options of a game. -/
def right : Game → List Game
  | mk _ r => r

@[simp] theorem left_mk (l r : List Game) : (mk l r).left = l := rfl
@[simp] theorem right_mk (l r : List Game) : (mk l r).right = r := rfl

theorem sizeOf_lt_of_mem_left {l r : List Game} {x : Game} (h : x ∈ l) :
    sizeOf x < sizeOf (mk l r) := by
  have := List.sizeOf_lt_of_mem h
  simp only [mk.sizeOf_spec]
  omega

theorem sizeOf_lt_of_mem_right {l r : List Game} {x : Game} (h : x ∈ r) :
    sizeOf x < sizeOf (mk l r) := by
  have := List.sizeOf_lt_of_mem h
  simp only [mk.sizeOf_spec]
  omega

/-- The game `0 = { | }`. -/
def zero : Game := mk [] []

/-- Conway's order: `le G H` means `G ≤ H`, i.e. no Left option `Gᴸ` satisfies `H ≤ Gᴸ`
and no Right option `Hᴿ` satisfies `Hᴿ ≤ G`. -/
def le : Game → Game → Prop
  | mk gl gr, mk hl hr =>
      (∀ x : {x // x ∈ gl}, ¬ le (mk hl hr) x.1) ∧ (∀ y : {y // y ∈ hr}, ¬ le y.1 (mk gl gr))
termination_by g h => sizeOf g + sizeOf h
decreasing_by
  · have := sizeOf_lt_of_mem_left (r := gr) x.2
    omega
  · have := sizeOf_lt_of_mem_right (l := hl) y.2
    omega

theorem le_mk_iff {gl gr hl hr : List Game} :
    le (mk gl gr) (mk hl hr) ↔
      (∀ x ∈ gl, ¬ le (mk hl hr) x) ∧ (∀ y ∈ hr, ¬ le y (mk gl gr)) := by
  rw [le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx => h1 ⟨x, hx⟩, fun y hy => h2 ⟨y, hy⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 x.1 x.2, fun y => h2 y.1 y.2⟩

theorem le_iff {g h : Game} :
    le g h ↔ (∀ x ∈ g.left, ¬ le h x) ∧ (∀ y ∈ h.right, ¬ le y g) := by
  cases g; cases h; exact le_mk_iff

/-- `lt G H` means `G < H`, i.e. `G ≤ H` and not `H ≤ G`. -/
def lt (g h : Game) : Prop := le g h ∧ ¬ le h g

/-- Game equivalence `G = H` in the sense of combinatorial game theory. -/
def Equiv (g h : Game) : Prop := le g h ∧ le h g

theorem not_le_of_mem_left {g x : Game} (hx : x ∈ g.left) (h : le g x) : ¬ le x x := by
  rw [le_iff] at h
  exact h.1 x hx

theorem le_refl : ∀ g : Game, le g g
  | mk l r => by
    rw [le_mk_iff]
    refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
    · have ih := le_refl x
      rw [le_iff] at hle
      exact hle.1 x hx ih
    · have ih := le_refl y
      rw [le_iff] at hle
      exact hle.2 y hy ih
termination_by g => sizeOf g
decreasing_by
  · exact sizeOf_lt_of_mem_left hx
  · exact sizeOf_lt_of_mem_right hy

/-- A Left option of `g` is never `≥ g`. -/
theorem not_le_left {g x : Game} (hx : x ∈ g.left) : ¬ le g x := by
  have h := le_refl g
  rw [le_iff] at h
  exact h.1 x hx

/-- A Right option of `g` is never `≤ g`. -/
theorem not_right_le {g y : Game} (hy : y ∈ g.right) : ¬ le y g := by
  have h := le_refl g
  rw [le_iff] at h
  exact h.2 y hy

theorem le_trans : ∀ g h k : Game, le g h → le h k → le g k
  | mk gl gr, mk hl hr, mk kl kr => by
    intro h1 h2
    rw [le_mk_iff] at h1 h2 ⊢
    refine ⟨fun x hx hkx => ?_, fun z hz hzg => ?_⟩
    · -- `k ≤ x` and `h ≤ k` give `h ≤ x`, contradicting `g ≤ h`.
      have := le_trans (mk hl hr) (mk kl kr) x (by rw [le_mk_iff]; exact h2) hkx
      exact h1.1 x hx this
    · -- `z ≤ g` and `g ≤ h` give `z ≤ h`, contradicting `h ≤ k`.
      have := le_trans z (mk gl gr) (mk hl hr) hzg (by rw [le_mk_iff]; exact h1)
      exact h2.2 z hz this
termination_by g h k => sizeOf g + sizeOf h + sizeOf k
decreasing_by
  · have := sizeOf_lt_of_mem_left (r := gr) hx
    omega
  · have := sizeOf_lt_of_mem_right (l := kl) hz
    omega

theorem lt_of_le_of_lt {g h k : Game} (h1 : le g h) (h2 : lt h k) : lt g k :=
  ⟨le_trans _ _ _ h1 h2.1, fun hkg => h2.2 (le_trans _ _ _ hkg h1)⟩

theorem lt_of_lt_of_le {g h k : Game} (h1 : lt g h) (h2 : le h k) : lt g k :=
  ⟨le_trans _ _ _ h1.1 h2, fun hkg => h1.2 (le_trans _ _ _ h2 hkg)⟩

theorem Equiv.refl (g : Game) : Equiv g g := ⟨le_refl g, le_refl g⟩
theorem Equiv.symm {g h : Game} (e : Equiv g h) : Equiv h g := ⟨e.2, e.1⟩
theorem Equiv.trans {g h k : Game} (e : Equiv g h) (f : Equiv h k) : Equiv g k :=
  ⟨le_trans _ _ _ e.1 f.1, le_trans _ _ _ f.2 e.2⟩

/-- If every option of each game is matched by an equivalent option of the other game
(on the same side), the games are equivalent. -/
theorem equiv_of_options {gl gr hl hr : List Game}
    (hl1 : ∀ x ∈ gl, ∃ x' ∈ hl, Equiv x x') (hl2 : ∀ x' ∈ hl, ∃ x ∈ gl, Equiv x' x)
    (hr1 : ∀ y ∈ gr, ∃ y' ∈ hr, Equiv y y') (hr2 : ∀ y' ∈ hr, ∃ y ∈ gr, Equiv y' y) :
    Equiv (mk gl gr) (mk hl hr) := by
  have key : ∀ {al ar bl br : List Game},
      (∀ x ∈ al, ∃ x' ∈ bl, Equiv x x') → (∀ y' ∈ br, ∃ y ∈ ar, Equiv y' y) →
      le (mk al ar) (mk bl br) := by
    intro al ar bl br h1 h2
    rw [le_mk_iff]
    refine ⟨fun x hx hle => ?_, fun y' hy' hle => ?_⟩
    · obtain ⟨x', hx', e⟩ := h1 x hx
      exact not_le_left (g := mk bl br) hx' (le_trans _ _ _ hle e.1)
    · obtain ⟨y, hy, e⟩ := h2 y' hy'
      exact not_right_le (g := mk al ar) hy (le_trans _ _ _ e.2 hle)
  exact ⟨key hl1 hr2, key hl2 hr1⟩

/-! ### Negation -/

/-- The negative of a game: swap the roles of Left and Right. -/
def neg : Game → Game
  | mk l r => mk (r.attach.map fun y => neg y.1) (l.attach.map fun x => neg x.1)
termination_by g => sizeOf g
decreasing_by
  · exact sizeOf_lt_of_mem_right y.2
  · exact sizeOf_lt_of_mem_left x.2

theorem neg_mk (l r : List Game) :
    neg (mk l r) = mk (r.attach.map fun y => neg y.1) (l.attach.map fun x => neg x.1) := by
  rw [neg]

theorem mem_left_neg {g z : Game} : z ∈ (neg g).left ↔ ∃ y ∈ g.right, z = neg y := by
  cases g with
  | mk l r =>
    rw [neg_mk]
    simp only [left_mk, right_mk, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem mem_right_neg {g z : Game} : z ∈ (neg g).right ↔ ∃ x ∈ g.left, z = neg x := by
  cases g with
  | mk l r =>
    rw [neg_mk]
    simp only [left_mk, right_mk, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem sizeOf_lt_of_mem_left' {g x : Game} (h : x ∈ g.left) : sizeOf x < sizeOf g := by
  cases g; exact sizeOf_lt_of_mem_left h

theorem sizeOf_lt_of_mem_right' {g x : Game} (h : x ∈ g.right) : sizeOf x < sizeOf g := by
  cases g; exact sizeOf_lt_of_mem_right h

/-- Negation reverses the order. -/
theorem neg_le_neg_iff (g h : Game) : le (neg g) (neg h) ↔ le h g := by
  induction hn : sizeOf g + sizeOf h using Nat.strongRecOn generalizing g h with
  | _ n ih =>
  rw [le_iff, le_iff (g := h)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx hgx => ?_, fun y hy hyh => ?_⟩
    · have hmem : neg x ∈ (neg h).right := mem_right_neg.2 ⟨x, hx, rfl⟩
      have hlt := sizeOf_lt_of_mem_left' hx
      have : le (neg x) (neg g) := (ih _ (by omega) x g rfl).2 hgx
      exact h2 _ hmem this
    · have hmem : neg y ∈ (neg g).left := mem_left_neg.2 ⟨y, hy, rfl⟩
      have hlt := sizeOf_lt_of_mem_right' hy
      have : le (neg h) (neg y) := (ih _ (by omega) h y rfl).2 hyh
      exact h1 _ hmem this
  · rintro ⟨h1, h2⟩
    refine ⟨fun z hz hle => ?_, fun z hz hle => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_left_neg.1 hz
      have hlt := sizeOf_lt_of_mem_right' hy
      exact h2 y hy ((ih _ (by omega) h y rfl).1 hle)
    · obtain ⟨x, hx, rfl⟩ := mem_right_neg.1 hz
      have hlt := sizeOf_lt_of_mem_left' hx
      exact h1 x hx ((ih _ (by omega) x g rfl).1 hle)

end Game
end Cgt
