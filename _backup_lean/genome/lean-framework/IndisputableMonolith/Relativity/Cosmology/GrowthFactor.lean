import Mathlib
import IndisputableMonolith.Relativity.Cosmology.FRWMetric
import IndisputableMonolith.Relativity.Cosmology.Perturbations

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Geometry

structure GrowthFactor where
  D : ℝ → ℝ
  D_positive : ∀ a, 0 < a → 0 < D a

noncomputable def f_growth (growth : GrowthFactor) (a : ℝ) : ℝ :=
  a * deriv growth.D a / growth.D a

def GrowthEquation (growth : GrowthFactor) (scale : ScaleFactor) (Omega_m mu : ℝ → ℝ) : Prop :=
  ∀ a, let lna := Real.log a
       deriv (deriv growth.D) lna +
       (2 + deriv (Real.log ∘ hubble_parameter scale) lna) * deriv growth.D lna -
       (3/2) * Omega_m a * mu a * growth.D lna = 0

-- Note: These were axioms but are not used in any proofs. Converted to hypotheses.
def growth_equation_exists_hypothesis (scale : ScaleFactor) (Omega_m : ℝ → ℝ) : Prop :=
  ∃ mu : ℝ → ℝ, ∃ growth : GrowthFactor,
    GrowthEquation growth scale Omega_m mu

def modification_factor_GR_hypothesis (scale : ScaleFactor) (Omega_m : ℝ → ℝ) : Prop :=
  ∃ growth : GrowthFactor, GrowthEquation growth scale Omega_m (fun _ => 1)

def modification_factor_ILG_hypothesis (scale : ScaleFactor) (Omega_m : ℝ → ℝ) (α C_lag : ℝ) : Prop :=
  ∃ mu : ℝ → ℝ, ∃ growth : GrowthFactor,
    GrowthEquation growth scale Omega_m mu ∧
    (∀ a, |mu a - 1| < (α * C_lag))

end Cosmology
end Relativity
end IndisputableMonolith
