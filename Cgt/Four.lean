import Cgt.Certificate

/-!
# Positions with four pieces

A position with four pieces is described by its pieces `c₁ c₂ c₃ c₄` (left to right; `true` is a
toad, `false` a frog) and the five gaps `g₀ … g₄` of empty squares around them:
`□^g₀ c₁ □^g₁ c₂ □^g₂ c₃ □^g₃ c₄ □^g₄` (`P4.toList`).

Each piece has at most one move: a slide into the next square, or a jump over an adjacent
opposing piece. `P4.lm1` … `P4.lm4` give that move for piece `i` if it is a toad, `P4.rm1` …
`P4.rm4` if it is a frog. `leftMoves_toList` and `rightMoves_toList` show that these are exactly
the moves of `TF.leftMoves` / `TF.rightMoves` on the corresponding list of cells.
-/

namespace Cgt
open Cell TF Game

local notation "rep" => List.replicate

/-- `true` is a toad, `false` a frog. -/
def pc (b : Bool) : Cell := if b then T else F

@[simp] theorem pc_true : pc true = T := rfl
@[simp] theorem pc_false : pc false = F := rfl

structure P4 where
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  g0 : Nat
  g1 : Nat
  g2 : Nat
  g3 : Nat
  g4 : Nat
  deriving DecidableEq, Repr

namespace P4

def toList (p : P4) : List Cell :=
  rep p.g0 E ++ pc p.c1 :: (rep p.g1 E ++ pc p.c2 :: (rep p.g2 E ++ pc p.c3 :: (rep p.g3 E ++
    pc p.c4 :: rep p.g4 E)))

/-- The move of piece 1 if it is a toad. -/
def lm1 (p : P4) : Option P4 :=
  if p.c1 = true then
    if p.g1 ≠ 0 then some { p with g0 := p.g0 + 1, g1 := p.g1 - 1 }
    else if p.c2 = false ∧ p.g2 ≠ 0 then some { p with c1 := false, c2 := true, g0 := p.g0 + 1, g2 := p.g2 - 1 }
    else none
  else none

def lm2 (p : P4) : Option P4 :=
  if p.c2 = true then
    if p.g2 ≠ 0 then some { p with g1 := p.g1 + 1, g2 := p.g2 - 1 }
    else if p.c3 = false ∧ p.g3 ≠ 0 then some { p with c2 := false, c3 := true, g1 := p.g1 + 1, g3 := p.g3 - 1 }
    else none
  else none

def lm3 (p : P4) : Option P4 :=
  if p.c3 = true then
    if p.g3 ≠ 0 then some { p with g2 := p.g2 + 1, g3 := p.g3 - 1 }
    else if p.c4 = false ∧ p.g4 ≠ 0 then some { p with c3 := false, c4 := true, g2 := p.g2 + 1, g4 := p.g4 - 1 }
    else none
  else none

def lm4 (p : P4) : Option P4 :=
  if p.c4 = true ∧ p.g4 ≠ 0 then some { p with g3 := p.g3 + 1, g4 := p.g4 - 1 } else none

/-- The move of piece 1 if it is a frog. -/
def rm1 (p : P4) : Option P4 :=
  if p.c1 = false ∧ p.g0 ≠ 0 then some { p with g0 := p.g0 - 1, g1 := p.g1 + 1 } else none

def rm2 (p : P4) : Option P4 :=
  if p.c2 = false then
    if p.g1 ≠ 0 then some { p with g1 := p.g1 - 1, g2 := p.g2 + 1 }
    else if p.c1 = true ∧ p.g0 ≠ 0 then some { p with c1 := false, c2 := true, g0 := p.g0 - 1, g2 := p.g2 + 1 }
    else none
  else none

def rm3 (p : P4) : Option P4 :=
  if p.c3 = false then
    if p.g2 ≠ 0 then some { p with g2 := p.g2 - 1, g3 := p.g3 + 1 }
    else if p.c2 = true ∧ p.g1 ≠ 0 then some { p with c2 := false, c3 := true, g1 := p.g1 - 1, g3 := p.g3 + 1 }
    else none
  else none

def rm4 (p : P4) : Option P4 :=
  if p.c4 = false then
    if p.g3 ≠ 0 then some { p with g3 := p.g3 - 1, g4 := p.g4 + 1 }
    else if p.c3 = true ∧ p.g2 ≠ 0 then some { p with c3 := false, c4 := true, g2 := p.g2 - 1, g4 := p.g4 + 1 }
    else none
  else none

/-- All Left moves, in the order `TF.leftMoves` lists them. -/
def lms (p : P4) : List P4 := p.lm1.toList ++ p.lm2.toList ++ p.lm3.toList ++ p.lm4.toList

/-- All Right moves (as a set; the order is irrelevant). -/
def rms (p : P4) : List P4 := p.rm1.toList ++ p.rm2.toList ++ p.rm3.toList ++ p.rm4.toList

end P4

/-! ### Moves of one piece followed by a block of empty squares -/

/-- The head of `TF.leftMoves (c :: r)`: the move of the first cell. -/
def headL0 : Cell → List Cell → List (List Cell)
  | T, E :: r => [E :: T :: r]
  | T, F :: E :: r => [E :: F :: T :: r]
  | _, _ => []

theorem leftMoves_cons (c : Cell) (r : List Cell) :
    leftMoves (c :: r) = headL0 c r ++ (leftMoves r).map (c :: ·) := by
  cases c <;> rcases r with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, _⟩⟩ <;> rfl

theorem rep_succ_append' (k : Nat) (r : List Cell) : rep k E ++ E :: r = rep (k + 1) E ++ r := by
  rw [List.replicate_succ', List.append_assoc]; rfl

/-- The moves of a piece `c` followed by `g` empty squares and another piece `d`. -/
theorem leftMoves_piece (c d : Cell) (g : Nat) (Z : List Cell) :
    leftMoves (c :: (rep g E ++ d :: Z)) =
      headL0 c (rep g E ++ d :: Z) ++
        (leftMoves (d :: Z)).map (fun q => c :: (rep g E ++ q)) := by
  rw [leftMoves_cons, leftMoves_replicate_E_append, List.map_map]; rfl

theorem leftMoves_piece_last (c : Cell) (g : Nat) :
    leftMoves (c :: rep g E) = headL0 c (rep g E) := by
  rw [leftMoves_cons, leftMoves_replicate_E]; simp

theorem leftMoves_toList (p : P4) : leftMoves p.toList = p.lms.map P4.toList := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  simp only [P4.toList, P4.lms]
  rw [leftMoves_replicate_E_append, leftMoves_piece, leftMoves_piece,
    leftMoves_piece, leftMoves_piece_last]
  simp only [List.map_append, List.map_map, List.append_assoc]
  congr 1
  · simp only [P4.lm1]
    cases c1 <;> cases c2 <;> cases c3 <;> cases g1 <;> cases g2 <;>
      simp_all [headL0, pc, P4.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P4.lm2]
    cases c2 <;> cases c3 <;> cases c4 <;> cases g2 <;> cases g3 <;>
      simp_all [headL0, pc, P4.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P4.lm3]
    cases c3 <;> cases c4 <;> cases g3 <;> cases g4 <;>
      simp_all [headL0, pc, P4.toList, rep_succ_append', List.replicate_succ]
  · simp only [P4.lm4]
    cases c4 <;> cases g4 <;> simp_all [headL0, pc, P4.toList, rep_succ_append', List.replicate_succ]

/-- The head of `TF.rightMoves (c :: r)`: the move into the first cell. -/
def headR0 : Cell → List Cell → List (List Cell)
  | E, F :: r => [F :: E :: r]
  | E, T :: F :: r => [F :: T :: E :: r]
  | _, _ => []

theorem rightMoves_cons (c : Cell) (r : List Cell) :
    rightMoves (c :: r) = headR0 c r ++ (rightMoves r).map (c :: ·) := by
  cases c <;> rcases r with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, _⟩⟩ <;> rfl

theorem pc_ne (b : Bool) : pc b ≠ E := by cases b <;> simp [pc]

/-- Right moves of a block of `g` empty squares followed by a piece `c`. -/
def segR (g : Nat) (c : Cell) (Y : List Cell) : List (List Cell) :=
  match g with
  | 0 => []
  | k + 1 => (headR0 E (c :: Y)).map (rep k E ++ ·)

theorem rightMoves_seg (g : Nat) (c : Cell) (Y : List Cell) (hc : c ≠ E) :
    rightMoves (rep g E ++ c :: Y) = segR g c Y ++ (rightMoves Y).map (fun q => rep g E ++ c :: q) := by
  induction g with
  | zero =>
    rw [List.replicate_zero, List.nil_append, rightMoves_cons]
    cases c <;> simp_all [headR0, segR]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [Nat.zero_add, List.replicate_one, List.singleton_append]
      rw [rightMoves_cons, rightMoves_cons]; cases c <;> simp_all [headR0, segR, Function.comp_def]
    | succ k =>
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append, rightMoves_E_E,
        ← List.cons_append, ← List.replicate_succ, ih]
      simp [segR, List.map_map, Function.comp_def, List.replicate_succ]

theorem rightMoves_toList (p : P4) : rightMoves p.toList = p.rms.map P4.toList := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  simp only [P4.toList, P4.rms]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3),
    rightMoves_seg _ _ _ (pc_ne c4), rightMoves_replicate_E]
  simp only [List.map_nil, List.append_nil, List.map_append, List.map_map, List.append_assoc]
  simp only [P4.rm1, P4.rm2, P4.rm3, P4.rm4]
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;>
    cases g0 <;> cases g1 <;> cases g2 <;> cases g3 <;> cases g4 <;>
    simp_all [segR, headR0, pc, P4.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves {p q : P4} (h : q ∈ p.rms) :
    q.toList ∈ rightMoves p.toList := by
  rw [rightMoves_toList p]; exact List.mem_map_of_mem h

end Cgt
