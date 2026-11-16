import Cgt.Col.Check

/-!
# Key trees from run-length text

For certificates too large to write out as Lean terms (the column `b = 4`), the data is a text with
one witness position per key, and the key trees are computed from it:

* a witness is written run by run, as a cell letter (`T`, `F`, `E`) followed by the run length,
  e.g. `T4E4F4` for `TTTT□□□□FFFF`; witnesses are separated by `;`;
* `keysOfText r s` computes the key `keyOf r` of every witness;
* `treeOfKeys` sorts the keys and builds a balanced search tree.

Nothing about these functions needs to be proved: the soundness theorem `sound` holds for any
trees, and the finite check is run on the trees they produce.
-/

namespace Cgt
namespace Col
open Cell

def cellOfChar (c : Char) : Cell := if c = 'T' then T else if c = 'F' then F else E

def parseRLAux : List Char → Option Cell → Nat → RL → RL
  | [], none, _, acc => acc.reverse
  | [], some c, n, acc => ((c, n) :: acc).reverse
  | ch :: cs, cur, n, acc =>
    if ch.isDigit then parseRLAux cs cur (10 * n + (ch.toNat - '0'.toNat)) acc
    else match cur with
      | none => parseRLAux cs (some (cellOfChar ch)) 0 acc
      | some c => parseRLAux cs (some (cellOfChar ch)) 0 ((c, n) :: acc)

/-- Parse one witness, e.g. `T4E4F4`. -/
def parseRL (s : String) : RL := parseRLAux s.toList none 0 []

/-- The keys of the `;`-separated witnesses of the given texts. -/
def keysOfText (r : GapRule) (parts : List String) : Array (List Nat) :=
  (parts.flatMap fun s => (s.splitOn ";").filter (fun w => !w.isEmpty)).toArray.map fun w => keyOf r (parseRL w)

/-- A balanced tree of the keys `a[lo .. hi)`. -/
def treeOfSorted (a : Array (List Nat)) (lo hi : Nat) : LTree :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    LTree.node (treeOfSorted a lo mid) (a.getD mid []) (treeOfSorted a (mid + 1) hi)
  else LTree.leaf
termination_by hi - lo

/-- A balanced search tree of the given keys. -/
def treeOfKeys (a : Array (List Nat)) : LTree :=
  let b := a.qsort fun x y => lexLt x y
  treeOfSorted b 0 b.size

end Col
end Cgt
