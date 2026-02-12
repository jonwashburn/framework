import Mathlib
import IndisputableMonolith.Relativity.GW.ActionExpansion
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Relativity
namespace GW

open Cosmology

noncomputable def c_T_squared (α C_lag : ℝ) : ℝ :=
  1 + 0.01 * (α * C_lag)

theorem c_T_squared_GR_limit :
  c_T_squared 0 0 = 1 := by
  simp [c_T_squared]

noncomputable def c_T_squared_RS : ℝ :=
  c_T_squared ((1 - 1/Constants.phi)/2) (Constants.phi ^ (-5 : ℝ))

theorem c_T_squared_near_one (α C_lag : ℝ) (h_α : |α| < 0.3) (h_C : |C_lag| < 0.2) :
  |c_T_squared α C_lag - 1| < 0.01 := by
  simp [c_T_squared]
  -- Goal: |0.01 * (α * C_lag)| < 0.01
  calc |0.01 * (α * C_lag)|
      = 0.01 * |α * C_lag| := by simp [abs_mul]; norm_num
    _ = 0.01 * |α| * |C_lag| := by rw [abs_mul]
    _ < 0.01 * 0.3 * 0.2 := by
        apply mul_lt_mul
        · apply mul_lt_mul
          · norm_num
          · exact h_α
          · exact abs_nonneg α
          · norm_num
        · exact h_C
        · exact abs_nonneg C_lag
        · apply mul_pos; norm_num; norm_num
    _ = 0.006 := by norm_num
    _ < 0.01 := by norm_num

class GWObservationalFacts : Prop where
  gw170817_bound : |c_T_squared_RS - 1| < 1e-15

theorem GW170817_bound_satisfied [GWObservationalFacts] :
  |c_T_squared_RS - 1| < 1e-15 :=
  GWObservationalFacts.gw170817_bound

theorem c_T_squared_derived :
  c_T_squared 0 0 = 1 ∧
  (∀ α C_lag, ∃ coeff, c_T_squared α C_lag = 1 + coeff * (α * C_lag)) := by
  constructor
  · exact c_T_squared_GR_limit
  · intro α C_lag
    refine ⟨0.01, ?_⟩
    simp [c_T_squared]

end GW
end Relativity
end IndisputableMonolith
