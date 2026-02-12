import IndisputableMonolith.Biology.MetabolicScaling

/-!
Demo: Metabolic Scaling ¾-Law

#eval L * M^{3/4} constant.
-/

namespace IndisputableMonolith
namespace Biology

#check three_quarters_holds

#eval s!"L for M=1: {metabolic_rate 1}, M=10: {metabolic_rate 10} (check M^{3/4} product constant)"

end Biology
end IndisputableMonolith
