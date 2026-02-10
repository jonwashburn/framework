import IndisputableMonolith.Biology.EnzymeRates

/-!
Demo: Enzyme Rate Ceilings

#eval k_cat ≤ φ^{-1} ~0.618 from J-min.
-/

namespace IndisputableMonolith
namespace Biology

#check ceiling_holds

#eval s!"Rate ceiling for r=1: {rate_ceiling 1} (≤ φ^{-1} ~0.618)"

end Biology
end IndisputableMonolith
