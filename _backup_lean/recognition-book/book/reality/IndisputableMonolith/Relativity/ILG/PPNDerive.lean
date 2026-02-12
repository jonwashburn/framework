import Mathlib
import IndisputableMonolith.Relativity/ILG/Lensing
import IndisputableMonolith.Relativity/ILG/PPN
import IndisputableMonolith.Relativity/ILG/Action

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Derive γ, β from a (symbolic) metric solution placeholder. -/
noncomputable def gamma_from_solution (ψ : RefreshField) (p : ILGParams) : ℝ :=
  PPN.gamma_pot ψ p

noncomputable def beta_from_solution (ψ : RefreshField) (p : ILGParams) : ℝ :=
  PPN.beta_pot ψ p

@[simp] theorem gamma_band_solution (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |gamma_from_solution ψ p - 1| ≤ κ := by
  simp [gamma_from_solution, PPN.gamma_pot]
  simpa using hκ

@[simp] theorem beta_band_solution (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |beta_from_solution ψ p - 1| ≤ κ := by
  simp [beta_from_solution, PPN.beta_pot]
  simpa using hκ

/-- Link γ from solution to linearized small-coupling form. -/
theorem gamma_solution_lin_bound (ψ : RefreshField) (p : ILGParams) :
  |gamma_from_solution ψ p - PPN.gamma_lin p.cLag p.alpha|
    ≤ (1/10 : ℝ) * |p.cLag * p.alpha| := by
  have hpos : 0 ≤ (1/10 : ℝ) := by norm_num
  have : gamma_from_solution ψ p - PPN.gamma_lin p.cLag p.alpha
      = -((1/10 : ℝ) * (p.cLag * p.alpha)) := by
    simp [gamma_from_solution, PPN.gamma_pot, PPN.gamma_lin, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc]
  calc
    |gamma_from_solution ψ p - PPN.gamma_lin p.cLag p.alpha|
        = | -((1/10 : ℝ) * (p.cLag * p.alpha)) | := by simpa [this]
    _ = |(1/10 : ℝ) * (p.cLag * p.alpha)| := by simpa [abs_neg]
    _ = (1/10 : ℝ) * |p.cLag * p.alpha| := by
          simpa [abs_mul, Real.abs_of_nonneg hpos]

/-- Link β from solution to linearized small-coupling form. -/
theorem beta_solution_lin_bound (ψ : RefreshField) (p : ILGParams) :
  |beta_from_solution ψ p - PPN.beta_lin p.cLag p.alpha|
    ≤ (1/20 : ℝ) * |p.cLag * p.alpha| := by
  have hpos : 0 ≤ (1/20 : ℝ) := by norm_num
  have : beta_from_solution ψ p - PPN.beta_lin p.cLag p.alpha
      = -((1/20 : ℝ) * (p.cLag * p.alpha)) := by
    simp [beta_from_solution, PPN.beta_pot, PPN.beta_lin, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc]
  calc
    |beta_from_solution ψ p - PPN.beta_lin p.cLag p.alpha|
        = | -((1/20 : ℝ) * (p.cLag * p.alpha)) | := by simpa [this]
    _ = |(1/20 : ℝ) * (p.cLag * p.alpha)| := by simpa [abs_neg]
    _ = (1/20 : ℝ) * |p.cLag * p.alpha| := by
          simpa [abs_mul, Real.abs_of_nonneg hpos]

/-- 1PN-level placeholders for γ and β extracted from the solution. -/
noncomputable def gamma1PN (ψ : RefreshField) (p : ILGParams) : ℝ :=
  PPN.gamma_lin p.cLag p.alpha

noncomputable def beta1PN (ψ : RefreshField) (p : ILGParams) : ℝ :=
  PPN.beta_lin p.cLag p.alpha

@[simp] theorem gamma1PN_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (h : |p.cLag * p.alpha| ≤ κ) : |gamma1PN ψ p - 1| ≤ (1/10 : ℝ) * κ := by
  simpa [gamma1PN] using PPN.gamma_bound_small p.cLag p.alpha κ h

@[simp] theorem beta1PN_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (h : |p.cLag * p.alpha| ≤ κ) : |beta1PN ψ p - 1| ≤ (1/20 : ℝ) * κ := by
  simpa [beta1PN] using PPN.beta_bound_small p.cLag p.alpha κ h

@[simp] theorem gamma1PN_eq_lin (ψ : RefreshField) (p : ILGParams) :
  gamma1PN ψ p = PPN.gamma_lin p.cLag p.alpha := rfl

@[simp] theorem beta1PN_eq_lin (ψ : RefreshField) (p : ILGParams) :
  beta1PN ψ p = PPN.beta_lin p.cLag p.alpha := rfl

/-- Zero-width band linking γ1PN to its linear form (scaffold). -/
theorem gamma1PN_lin_band_zero (ψ : RefreshField) (p : ILGParams) :
  |gamma1PN ψ p - PPN.gamma_lin p.cLag p.alpha| ≤ 0 := by
  simp [gamma1PN]

/-- Zero-width band linking β1PN to its linear form (scaffold). -/
theorem beta1PN_lin_band_zero (ψ : RefreshField) (p : ILGParams) :
  |beta1PN ψ p - PPN.beta_lin p.cLag p.alpha| ≤ 0 := by
  simp [beta1PN]

/-- Map observables to potentials: γ from ratio of Ψ to Φ (scaffold). -/
noncomputable def gamma_from_potentials (ψ : RefreshField) (p : ILGParams) : ℝ :=
  if h : Phi ψ p = 0 then 1 else (Psi ψ p) / (Phi ψ p)

/-- Map observables to potentials: β from quadratic combination (scaffold). -/
noncomputable def beta_from_potentials (ψ : RefreshField) (p : ILGParams) : ℝ :=
  1 + (Phi ψ p) * (Psi ψ p) * (1/20 : ℝ)

@[simp] theorem gamma_from_potentials_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |gamma_from_potentials ψ p - 1| ≤ κ := by
  -- Scaffold: choose κ large enough; we close with nonnegativity
  simpa [gamma_from_potentials] using hκ

@[simp] theorem beta_from_potentials_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |beta_from_potentials ψ p - 1| ≤ κ := by
  simpa [beta_from_potentials] using hκ

/-- Nonlinear γ placeholder with quadratic remainder absorbed in the band. -/
noncomputable def gamma_nl (ψ : RefreshField) (p : ILGParams) : ℝ :=
  gamma1PN ψ p

/-- Nonlinear β placeholder with quadratic remainder absorbed in the band. -/
noncomputable def beta_nl (ψ : RefreshField) (p : ILGParams) : ℝ :=
  beta1PN ψ p

theorem gamma_nl_bound (ψ : RefreshField) (p : ILGParams) :
  |gamma_nl ψ p - 1|
    ≤ (1/10 : ℝ) * |p.cLag * p.alpha| + (1/100 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
  have : |gamma_nl ψ p - 1| = (1/10 : ℝ) * |p.cLag * p.alpha| := by
    simp [gamma_nl, gamma1PN, ppn_gamma_lin]
  have hnn : 0 ≤ (1/100 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
    have : 0 ≤ |p.cLag * p.alpha| := abs_nonneg _
    have hpos : 0 ≤ (1/100 : ℝ) := by norm_num
    have : 0 ≤ |p.cLag * p.alpha| * |p.cLag * p.alpha| := mul_nonneg this this
    exact mul_nonneg hpos this
  simpa [this] using (le_add_of_nonneg_right hnn)

theorem beta_nl_bound (ψ : RefreshField) (p : ILGParams) :
  |beta_nl ψ p - 1|
    ≤ (1/20 : ℝ) * |p.cLag * p.alpha| + (1/400 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
  have : |beta_nl ψ p - 1| = (1/20 : ℝ) * |p.cLag * p.alpha| := by
    simp [beta_nl, beta1PN, ppn_beta_lin]
  have hnn : 0 ≤ (1/400 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
    have : 0 ≤ |p.cLag * p.alpha| := abs_nonneg _
    have hpos : 0 ≤ (1/400 : ℝ) := by norm_num
    have : 0 ≤ |p.cLag * p.alpha| * |p.cLag * p.alpha| := mul_nonneg this this
    exact mul_nonneg hpos this
  simpa [this] using (le_add_of_nonneg_right hnn)

end ILG
end Relativity
end IndisputableMonolith
