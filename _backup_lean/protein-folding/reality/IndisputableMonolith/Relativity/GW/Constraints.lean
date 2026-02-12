import Mathlib
import IndisputableMonolith.Relativity.GW.PropagationSpeed

namespace IndisputableMonolith
namespace Relativity
namespace GW

def gw170817_bound : ℝ := 1e-15

axiom coupling_bound_from_GW170817 (α C_lag : ℝ) :
  |c_T_squared α C_lag - 1| < gw170817_bound →
  |α * C_lag| < gw170817_bound / 0.01

axiom RS_satisfies_GW_bound :
  |c_T_squared_RS - 1| < gw170817_bound

theorem GW_constraint_framework :
  ∃ bound, bound = gw170817_bound ∧ bound < 0.001 := by
  refine ⟨gw170817_bound, rfl, ?_⟩
  simp [gw170817_bound]
  norm_num

end GW
end Relativity
end IndisputableMonolith
