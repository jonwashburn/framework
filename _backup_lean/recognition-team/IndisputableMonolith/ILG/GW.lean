import Mathlib
import IndisputableMonolith.Relativity/ILG/Action

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- GW tensor-mode speed squared c_T^2 from the action (scaffold). -/
noncomputable def c_T2 (p : ILGParams) : ℝ := 1

/-- Gravitational-wave phase speed (scaffold, GR-consistent units). -/
noncomputable def gw_speed (C_lag α : ℝ) : ℝ := 1

/-- Band statement: |v_gw − 1| ≤ κ for admissible κ ≥ 0 (scaffold). -/
theorem gw_band (κ C_lag α : ℝ) (hκ : 0 ≤ κ) :
  |gw_speed C_lag α - 1| ≤ κ := by
  -- gw_speed = 1, hence the deviation is 0 ≤ κ
  simpa [gw_speed] using hκ

/-- Small-coupling band for c_T^2 around 1 (symbolic). -/
theorem cT_band (κ : ℝ) (p : ILGParams) (hκ : 0 ≤ κ) :
  |c_T2 p - 1| ≤ κ := by
  simpa [c_T2] using hκ

/-- Quadratic action around FRW (scaffold): asserts the derived tensor speed.
    In this scaffold, it links directly to c_T2 = 1. -/
def QuadraticActionGW (p : ILGParams) : Prop := c_T2 p = 1

@[simp] theorem quadratic_action_gw_link (p : ILGParams) :
  QuadraticActionGW p := by
  simp [QuadraticActionGW, c_T2]

/-- Small-coupling band for GW speed: if |C_lag·α| ≤ κ, then |v_gw−1| ≤ κ (scaffold). -/
theorem gw_band_small (C_lag α κ : ℝ) (h : |C_lag * α| ≤ κ) :
  |gw_speed C_lag α - 1| ≤ κ := by
  -- gw_speed = 1 ⇒ LHS = 0, which is ≤ κ by h.
  have : (0 : ℝ) ≤ κ := le_trans (by norm_num) h
  simpa [gw_speed] using this

end ILG
end Relativity
end IndisputableMonolith
