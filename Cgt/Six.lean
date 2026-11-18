import Cgt.Four

/-!
# Positions with six pieces

A position with six pieces is described by its pieces `c₁ … c₆` (left to right; `true` is a toad,
`false` a frog) and the seven gaps `g₀ … g₆` of empty squares around them (`P6.toList`), as `P4`
does for four pieces (`Cgt/Four.lean`).

`P6.lm1` … `P6.lm6` give the move of piece `i` if it is a toad, `P6.rm1` … `P6.rm6` if it is a frog.
`leftMoves_toList6` shows that the `lm`s are exactly the Left moves of the list of cells, and
`toList_mem_rightMoves6` that every `rm` is a Right move of it.

-/

namespace Cgt
open Cell TF Game

local notation "rep" => List.replicate

structure P6 where
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  c5 : Bool
  c6 : Bool
  g0 : Nat
  g1 : Nat
  g2 : Nat
  g3 : Nat
  g4 : Nat
  g5 : Nat
  g6 : Nat
  deriving DecidableEq, Repr

namespace P6

def toList (p : P6) : List Cell :=
  rep p.g0 E ++ pc p.c1 :: (rep p.g1 E ++ pc p.c2 :: (rep p.g2 E ++ pc p.c3 :: (rep p.g3 E ++ pc p.c4 :: (rep p.g4 E ++ pc p.c5 :: (rep p.g5 E ++ pc p.c6 :: (rep p.g6 E))))))

def lm1 (p : P6) : Option P6 :=
  if p.c1 = true then
    if p.g1 ≠ 0 then some { p with g0 := p.g0 + 1, g1 := p.g1 - 1 }
    else if p.c2 = false ∧ p.g2 ≠ 0 then some { p with c1 := false, c2 := true, g0 := p.g0 + 1, g2 := p.g2 - 1 }
    else none
  else none

def lm2 (p : P6) : Option P6 :=
  if p.c2 = true then
    if p.g2 ≠ 0 then some { p with g1 := p.g1 + 1, g2 := p.g2 - 1 }
    else if p.c3 = false ∧ p.g3 ≠ 0 then some { p with c2 := false, c3 := true, g1 := p.g1 + 1, g3 := p.g3 - 1 }
    else none
  else none

def lm3 (p : P6) : Option P6 :=
  if p.c3 = true then
    if p.g3 ≠ 0 then some { p with g2 := p.g2 + 1, g3 := p.g3 - 1 }
    else if p.c4 = false ∧ p.g4 ≠ 0 then some { p with c3 := false, c4 := true, g2 := p.g2 + 1, g4 := p.g4 - 1 }
    else none
  else none

def lm4 (p : P6) : Option P6 :=
  if p.c4 = true then
    if p.g4 ≠ 0 then some { p with g3 := p.g3 + 1, g4 := p.g4 - 1 }
    else if p.c5 = false ∧ p.g5 ≠ 0 then some { p with c4 := false, c5 := true, g3 := p.g3 + 1, g5 := p.g5 - 1 }
    else none
  else none

def lm5 (p : P6) : Option P6 :=
  if p.c5 = true then
    if p.g5 ≠ 0 then some { p with g4 := p.g4 + 1, g5 := p.g5 - 1 }
    else if p.c6 = false ∧ p.g6 ≠ 0 then some { p with c5 := false, c6 := true, g4 := p.g4 + 1, g6 := p.g6 - 1 }
    else none
  else none

def lm6 (p : P6) : Option P6 :=
  if p.c6 = true ∧ p.g6 ≠ 0 then some { p with g5 := p.g5 + 1, g6 := p.g6 - 1 } else none

def rm1 (p : P6) : Option P6 :=
  if p.c1 = false ∧ p.g0 ≠ 0 then some { p with g0 := p.g0 - 1, g1 := p.g1 + 1 } else none

def rm2 (p : P6) : Option P6 :=
  if p.c2 = false then
    if p.g1 ≠ 0 then some { p with g1 := p.g1 - 1, g2 := p.g2 + 1 }
    else if p.c1 = true ∧ p.g0 ≠ 0 then some { p with c1 := false, c2 := true, g0 := p.g0 - 1, g2 := p.g2 + 1 }
    else none
  else none

def rm3 (p : P6) : Option P6 :=
  if p.c3 = false then
    if p.g2 ≠ 0 then some { p with g2 := p.g2 - 1, g3 := p.g3 + 1 }
    else if p.c2 = true ∧ p.g1 ≠ 0 then some { p with c2 := false, c3 := true, g1 := p.g1 - 1, g3 := p.g3 + 1 }
    else none
  else none

def rm4 (p : P6) : Option P6 :=
  if p.c4 = false then
    if p.g3 ≠ 0 then some { p with g3 := p.g3 - 1, g4 := p.g4 + 1 }
    else if p.c3 = true ∧ p.g2 ≠ 0 then some { p with c3 := false, c4 := true, g2 := p.g2 - 1, g4 := p.g4 + 1 }
    else none
  else none

def rm5 (p : P6) : Option P6 :=
  if p.c5 = false then
    if p.g4 ≠ 0 then some { p with g4 := p.g4 - 1, g5 := p.g5 + 1 }
    else if p.c4 = true ∧ p.g3 ≠ 0 then some { p with c4 := false, c5 := true, g3 := p.g3 - 1, g5 := p.g5 + 1 }
    else none
  else none

def rm6 (p : P6) : Option P6 :=
  if p.c6 = false then
    if p.g5 ≠ 0 then some { p with g5 := p.g5 - 1, g6 := p.g6 + 1 }
    else if p.c5 = true ∧ p.g4 ≠ 0 then some { p with c5 := false, c6 := true, g4 := p.g4 - 1, g6 := p.g6 + 1 }
    else none
  else none

/-- All Left moves, in the order `TF.leftMoves` lists them. -/
def lms (p : P6) : List P6 := p.lm1.toList ++ p.lm2.toList ++ p.lm3.toList ++ p.lm4.toList ++ p.lm5.toList ++ p.lm6.toList

/-- All Right moves. -/
def rms (p : P6) : List P6 := p.rm1.toList ++ p.rm2.toList ++ p.rm3.toList ++ p.rm4.toList ++ p.rm5.toList ++ p.rm6.toList

end P6

theorem leftMoves_toList6 (p : P6) : leftMoves p.toList = p.lms.map P6.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList, P6.lms]
  rw [leftMoves_replicate_E_append, leftMoves_piece, leftMoves_piece, leftMoves_piece, leftMoves_piece, leftMoves_piece, leftMoves_piece_last]
  simp only [List.map_append, List.map_map, List.append_assoc]
  congr 1
  · simp only [P6.lm1]
    cases c1 <;> cases c2 <;> cases c3 <;> cases g1 <;> cases g2 <;>
      simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P6.lm2]
    cases c2 <;> cases c3 <;> cases c4 <;> cases g2 <;> cases g3 <;>
      simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P6.lm3]
    cases c3 <;> cases c4 <;> cases c5 <;> cases g3 <;> cases g4 <;>
      simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P6.lm4]
    cases c4 <;> cases c5 <;> cases c6 <;> cases g4 <;> cases g5 <;>
      simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]
  congr 1
  · simp only [P6.lm5]
    cases c5 <;> cases c6 <;> cases g5 <;> cases g6 <;>
      simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]
  · simp only [P6.lm6]
    cases c6 <;> cases g6 <;> simp_all [headL0, pc, P6.toList, rep_succ_append', List.replicate_succ]

theorem toList_mem_rightMoves6_1 {p q : P6} (h : p.rm1 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c1 <;> cases g0 <;>
    simp [P6.rm1] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6_2 {p q : P6} (h : p.rm2 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c2 <;> cases g1 <;> cases c1 <;> cases g0 <;>
    simp [P6.rm2] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6_3 {p q : P6} (h : p.rm3 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c3 <;> cases g2 <;> cases c2 <;> cases g1 <;>
    simp [P6.rm3] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6_4 {p q : P6} (h : p.rm4 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c4 <;> cases g3 <;> cases c3 <;> cases g2 <;>
    simp [P6.rm4] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6_5 {p q : P6} (h : p.rm5 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c5 <;> cases g4 <;> cases c4 <;> cases g3 <;>
    simp [P6.rm5] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6_6 {p q : P6} (h : p.rm6 = some q) : q.toList ∈ rightMoves p.toList := by
  obtain ⟨c1, c2, c3, c4, c5, c6, g0, g1, g2, g3, g4, g5, g6⟩ := p
  simp only [P6.toList]
  rw [rightMoves_seg _ _ _ (pc_ne c1), rightMoves_seg _ _ _ (pc_ne c2), rightMoves_seg _ _ _ (pc_ne c3), rightMoves_seg _ _ _ (pc_ne c4), rightMoves_seg _ _ _ (pc_ne c5), rightMoves_seg _ _ _ (pc_ne c6), rightMoves_replicate_E]
  cases c6 <;> cases g5 <;> cases c5 <;> cases g4 <;>
    simp [P6.rm6] at h <;> subst h <;>
    simp [segR, headR0, pc, P6.toList, List.replicate_succ, Function.comp_def]

theorem toList_mem_rightMoves6 {p q : P6} (h : q ∈ p.rms) : q.toList ∈ rightMoves p.toList := by
  simp only [P6.rms, List.mem_append, Option.mem_toList] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact toList_mem_rightMoves6_1 h
  · exact toList_mem_rightMoves6_2 h
  · exact toList_mem_rightMoves6_3 h
  · exact toList_mem_rightMoves6_4 h
  · exact toList_mem_rightMoves6_5 h
  · exact toList_mem_rightMoves6_6 h

end Cgt
