import Cgt.Col.Runs

/-!
# Keys and witnesses for run lists

All definitions here are computable; the kernel evaluates them in the finite check.

* `deadB R i`: run `i` lies in a dead region: some toad run of length `≥ 2` at or before it and some
  frog run of length `≥ 2` at or after it, with no empty run in between (Erickson's dead pieces:
  these runs never move again).
* Entries: the live toad and frog runs of length `≥ 2`. Together with an anchor of value `2` they
  are sorted by (length, index); `sortE`.
* `keyOf r R`: the runs, each as its cell and its class (empty runs and runs of length 1 exactly;
  dead runs of length `≥ 2` only as "dead"; entries only as "long"), the sorted order of the
  entries, and the gaps between consecutive sorted lengths, recorded by the gap rule `r`: exactly
  up to `r.m`, above that only as "far", with the parity of the gap unless `r.par = 0`.
* `witOf r k`: the run lists with key `k` whose far gaps `c` are realised by `c`, `c + 2`, `c + 4`
  (with parity) or by `c`, `c + 1`, …, `c + 4` (without).

The column `b = 3` uses the rule `ruleP` (exact up to 2, parity above), the column `b = 4` the
rule `ruleF` (exact up to 1, only "far" above).
-/

namespace Cgt
namespace Col
open Cell

/-- The run at index `i` (a dummy empty run beyond the end). -/
def runAt (R : RL) (i : Nat) : Cell × Nat := R.getD i (E, 0)

def cellAt (R : RL) (i : Nat) : Cell := (runAt R i).1
def lenAt (R : RL) (i : Nat) : Nat := (runAt R i).2

/-- No empty run among the runs `i .. i + d`. -/
def noE (R : RL) (i d : Nat) : Bool := (List.range (d + 1)).all fun k => cellAt R (i + k) != E

/-- A toad run of length `≥ 2` at some `s ≤ i`, with no empty run in `s .. i`. -/
def leftDead (R : RL) (i : Nat) : Bool :=
  (List.range (i + 1)).any fun s => cellAt R s == T && decide (2 ≤ lenAt R s) && noE R s (i - s)

/-- A frog run of length `≥ 2` at some `e ≥ i` (inside the list), with no empty run in `i .. e`. -/
def rightDead (R : RL) (i : Nat) : Bool :=
  (List.range (R.length - i)).any fun d => cellAt R (i + d) == F && decide (2 ≤ lenAt R (i + d)) && noE R i d

def deadB (R : RL) (i : Nat) : Bool := leftDead R i && rightDead R i

/-- Entries: live toad or frog runs of length at least 2. -/
def isEntB (R : RL) (i : Nat) : Bool :=
  decide (i < R.length) && cellAt R i != E && decide (2 ≤ lenAt R i) && !deadB R i

/-! ### Sorting the entries -/

/-- Lexicographic order on (length, index). -/
def ltE (x y : Nat × Nat) : Bool := x.1 < y.1 || (x.1 == y.1 && x.2 < y.2)

def insertE (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: l => if ltE x y then x :: y :: l else y :: insertE x l

def sortE : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: l => insertE x (sortE l)

/-- The entries as (length, index), sorted. -/
def entries (R : RL) : List (Nat × Nat) :=
  sortE ((List.range R.length).filterMap fun i => if isEntB R i then some (lenAt R i, i) else none)

/-! ### Keys -/

/-- How a gap between consecutive sorted lengths is recorded: exactly up to `m`; above that only
as "far", together with its parity unless `par = 0`. -/
structure GapRule where
  m : Nat
  par : Nat

/-- The rule of the column `b = 3`: exact up to 2, parity above. -/
def ruleP : GapRule := ⟨2, 1⟩

/-- The rule of the column `b = 4`: exact up to 1, only "far" above. -/
def ruleF : GapRule := ⟨1, 0⟩

/-- Capped gap: exact up to `r.m`; above that `r.m + 1`, plus the parity if kept. -/
def capG (r : GapRule) (g : Nat) : Nat :=
  if g ≤ r.m then g else if r.par = 0 then r.m + 1 else r.m + 1 + (g - r.m - 1) % 2

def cellCode : Cell → Nat
  | E => 0
  | T => 1
  | F => 2

def codeCell : Nat → Cell
  | 1 => T
  | 2 => F
  | _ => E

/-- The class of a run: `0` dead and long, `1` an entry, `n + 2` exactly `n`. -/
def clsAt (R : RL) (i : Nat) : Nat :=
  if isEntB R i then 1 else if deadB R i && decide (2 ≤ lenAt R i) && cellAt R i != E then 0 else lenAt R i + 2

/-- Consecutive gaps along the sorted lengths, starting from the anchor `2`. -/
def gapsFrom : Nat → List (Nat × Nat) → List Nat
  | _, [] => []
  | p, x :: l => (x.1 - p) :: gapsFrom x.1 l

def keyOf (r : GapRule) (R : RL) : List Nat :=
  let es := entries R
  [R.length] ++ ((List.range R.length).flatMap fun i => [cellCode (cellAt R i), clsAt R i]) ++
    [es.length] ++ es.map Prod.snd ++ (gapsFrom 2 es).map (capG r)

/-! ### Witnesses -/

/-- The realisations of a capped gap: itself if exact; else `c`, `c + 2`, `c + 4` with parity
and `c`, `c + 1`, …, `c + 4` without. -/
def gapChoices (r : GapRule) (c : Nat) : List Nat :=
  if c ≤ r.m then [c] else if r.par = 0 then [c, c + 1, c + 2, c + 3, c + 4] else [c, c + 2, c + 4]

/-- All choice vectors for a list of capped gaps. -/
def choicesAll (r : GapRule) : List Nat → List (List Nat)
  | [] => [[]]
  | c :: cs => (gapChoices r c).flatMap fun g => (choicesAll r cs).map (g :: ·)

/-- Prefix sums from the anchor: the lengths of the sorted entries. -/
def prefixVals : Nat → List Nat → List Nat
  | _, [] => []
  | p, g :: gs => (p + g) :: prefixVals (p + g) gs

/-- The length given to run `i`: from its class, or from the sorted entries `idx` and `vals`. -/
def lenFor (cls : Nat) (idx vals : List Nat) (i : Nat) : Nat :=
  if cls = 0 then 2
  else if cls = 1 then ((idx.zip vals).find? (fun x => x.1 == i)).elim 0 Prod.snd
  else cls - 2

/-- Rebuild a run list from a key and a choice of realised gaps. -/
def build (k : List Nat) (gs : List Nat) : RL :=
  let L := k.headD 0
  let toks := (k.drop 1).take (2 * L)
  let ne := (k.drop (1 + 2 * L)).headD 0
  let idx := (k.drop (2 + 2 * L)).take ne
  let vals := prefixVals 2 gs
  (List.range L).map fun i =>
    (codeCell (toks.getD (2 * i) 0), lenFor (toks.getD (2 * i + 1) 0) idx vals i)

def witOf (r : GapRule) (k : List Nat) : List RL :=
  let L := k.headD 0
  let ne := (k.drop (1 + 2 * L)).headD 0
  let caps := (k.drop (2 + 2 * L + ne)).take ne
  (choicesAll r caps).map (build k)

end Col
end Cgt
