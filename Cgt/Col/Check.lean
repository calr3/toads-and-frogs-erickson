import Cgt.Col.Key

/-!
# The finite check for the column

Keys are stored in binary search trees (`LTree`, ordered lexicographically). `checkCol tU tN`
checks, for every witness `W` of every key in `tU` (Left stop phase) or `tN` (normal play):

* `U`: Left's pass and every Left move from `W` can be answered by Right's pass (the position's
  key is in `tN`) or by a Right move to a position whose key is in `tU`;
* `N`: every Left move from `W` has a Right reply whose key is in `tN`.
-/

namespace Cgt
namespace Col

/-- Lexicographic order on lists of numbers. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

inductive LTree where
  | leaf : LTree
  | node : LTree → List Nat → LTree → LTree

namespace LTree

def mem : LTree → List Nat → Bool
  | leaf, _ => false
  | node l x r, k => if k == x then true else if lexLt k x then mem l k else mem r k

def toList : LTree → List (List Nat)
  | leaf => []
  | node l x r => toList l ++ x :: toList r

theorem mem_toList : ∀ {t : LTree} {k : List Nat}, mem t k = true → k ∈ toList t
  | leaf, _, h => by simp [mem] at h
  | node l x r, k, h => by
    unfold mem at h
    by_cases hk : (k == x) = true
    · have := beq_iff_eq.1 hk; simp [toList, this]
    · rw [if_neg hk] at h
      by_cases hl : lexLt k x = true
      · rw [if_pos hl] at h; simp [toList, mem_toList h]
      · rw [if_neg hl] at h; simp [toList, mem_toList h]

end LTree

/-- Right, to move at `Y` and still holding his pass, can pass (key in `tN`) or reply into `tU`. -/
def lfOK (tU tN : LTree) (Y : RL) : Bool :=
  tN.mem (keyOf Y) || (rmovesR Y).any fun Z => tU.mem (keyOf Z)

def chkU (tU tN : LTree) (W : RL) : Bool := lfOK tU tN W && (lmovesR W).all (lfOK tU tN)

def chkN (tN : LTree) (W : RL) : Bool :=
  (lmovesR W).all fun X => (rmovesR X).any fun Z => tN.mem (keyOf Z)

def checkCol (tU tN : LTree) : Bool :=
  tU.toList.all (fun k => (witOf k).all (chkU tU tN)) && tN.toList.all (fun k => (witOf k).all (chkN tN))

/-- A check of the range `s .. s + cs.sum` of a list, split into consecutive chunks of sizes `cs`. -/
theorem all_range_of_sizes {α : Type} (p : α → Bool) :
    ∀ (cs : List Nat) (l : List α) (s : Nat),
      (∀ i, i < cs.length → ((l.drop (s + (cs.take i).sum)).take (cs.getD i 0)).all p = true) →
      ((l.drop s).take cs.sum).all p = true
  | [], _, _, _ => by simp
  | c :: cs, l, s, h => by
    rw [List.sum_cons, List.take_add, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    rw [List.drop_drop]
    refine all_range_of_sizes p cs l (s + c) (fun i hi => ?_)
    have := h (i + 1) (by simp; omega)
    simpa [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using this

end Col
end Cgt
