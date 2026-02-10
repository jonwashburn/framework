import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith/Compat

open Real Complex
open scoped BigOperators Matrix

/-!
Superconducting Tc scaling families from a φ-gap ladder proxy.

We model a monotone family `tc_phonon n = (1/φ)^n` to capture the
decrease of Tc with ladder step `n`. This suffices for a compiling,
dimensionless monotonicity result used by certificates and reports.
-/

namespace IndisputableMonolith
namespace Chemistry

/-- Phonon-route Tc proxy at ladder step `n`. -/
noncomputable def tc_phonon (n : Nat) : ℝ := (1 / Constants.phi) ^ n

/-- Tc decreases with ladder step: if `n₁ < n₂` then `tc_phonon n₁ > tc_phonon n₂`. -/
theorem tc_scaling (n₁ n₂ : Nat) (h : n₁ < n₂) : tc_phonon n₁ > tc_phonon n₂ := by
  dsimp [tc_phonon]
  -- Base `a = 1/φ` satisfies 0 < a < 1
  have hφpos : 0 < Constants.phi := by
    have : 1 < Constants.phi := Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  have ha_pos : 0 < (1 / Constants.phi) := inv_pos.mpr hφpos
  have ha_nonneg : 0 ≤ (1 / Constants.phi) := le_of_lt ha_pos
  have ha_lt_one : (1 / Constants.phi) < 1 := by
    -- From 1 < φ and φ > 0, `1 / φ < 1` via `div_lt_iff`
    have hiff : (1 : ℝ) / Constants.phi < 1 ↔ (1 : ℝ) < 1 * Constants.phi :=
      div_lt_iff hφpos
    have : (1 : ℝ) < 1 * Constants.phi := by
      simpa [one_mul] using (Constants.one_lt_phi : 1 < Constants.phi)
    have : (1 : ℝ) / Constants.phi < 1 := hiff.mpr this
    simpa [one_div] using this
  -- Write n₂ = n₁ + k with k = n₂ - n₁ > 0
  have hle : n₁ ≤ n₂ := Nat.le_of_lt h
  have hn2 : n₁ + (n₂ - n₁) = n₂ := Nat.add_sub_of_le hle
  have hkpos : 0 < n₂ - n₁ := Nat.sub_pos_of_lt h
  -- a^(n₂) = a^(n₁) * a^k and a^k < 1 because 0 ≤ a < 1 and k>0
  have hpowlt : (1 / Constants.phi) ^ (n₂ - n₁) < 1 :=
    pow_lt_one ha_nonneg ha_lt_one hkpos
  have hpowpos : 0 < (1 / Constants.phi) ^ n₁ :=
    pow_pos ha_pos _
  -- Compare by multiplying the left positive factor a^(n₁)
  have : (1 / Constants.phi) ^ (n₁ + (n₂ - n₁))
           = (1 / Constants.phi) ^ n₁ * (1 / Constants.phi) ^ (n₂ - n₁) := by
    simpa [pow_add]
  -- Conclude strict inequality
  have hmul : (1 / Constants.phi) ^ n₁
                * (1 / Constants.phi) ^ (n₂ - n₁)
              < (1 / Constants.phi) ^ n₁ * 1 :=
    (mul_lt_mul_of_pos_left hpowlt hpowpos)
  simpa [this, hn2, mul_one]

end Chemistry
end IndisputableMonolith
