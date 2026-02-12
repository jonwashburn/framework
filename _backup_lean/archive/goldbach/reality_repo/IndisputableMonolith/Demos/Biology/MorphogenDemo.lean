import IndisputableMonolith.Biology.Morphogen

/-!
Demo: Morphogen Gradient Precision

#eval precision >0 from φ-floor.
-/

namespace IndisputableMonolith
namespace Biology

#check precision_holds

#eval s!"Precision for noise={Constants.E_coh}, scale=1: {morphogen_precision Constants.E_coh 1} ~11 (Turing-like)"

end Biology
end IndisputableMonolith
