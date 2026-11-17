import Cgt.Col.Key

/-!
# The gap rule of the exact values of the column `b = 4`

`ruleF2`: gaps between sorted lengths are exact up to 2 and above that only "far", without
parity. The infinitesimal proof of `b = 4` uses `ruleF` (exact up to 1); the exact values need the
gap `a - 2 = 2` of the start `T⁴□⁴F⁴` (value `0`) to be told apart from the starts with `a ≥ 5`
(value `∗`).
-/

namespace Cgt
namespace Col

def ruleF2 : GapRule := ⟨2, 0⟩

end Col
end Cgt
