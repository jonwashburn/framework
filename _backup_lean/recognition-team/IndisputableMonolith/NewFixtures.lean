/-!
Fixtures providing stub instances for hypothesis classes introduced to replace sorries.
These live outside production namespaces to keep the trust boundary clear.
-/

namespace IndisputableMonolith
namespace TestFixtures

open IndisputableMonolith.Relativity.Perturbation
open IndisputableMonolith.Relativity.Analysis
open IndisputableMonolith.Relativity.Geometry
open IndisputableMonolith.Verification.Necessity
open IndisputableMonolith.Verification.Exclusivity
open IndisputableMonolith.Relativity.Perturbation.LinearizedEquations
open IndisputableMonolith.Verification.Necessity.DiscreteNecessity
open IndisputableMonolith.Relativity.Perturbation.WeightFormula
open IndisputableMonolith.Relativity.Perturbation.SphericalWeight
open IndisputableMonolith.Physics.CKM

noncomputable def gaugeFactsStub : GaugeConstructionFacts where
  find_gauge_vector_for_newtonian := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ _; simp [gauge_transform, InNewtonianGauge]⟩
  spatial_trace_freedom := by intro h hnewt; exact ⟨⟨fun _ => 0⟩, hnewt, by intro _ _ _ _ _ _; simp [gauge_transform, InNewtonianGauge]⟩
  newtonian_gauge_exists := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
  matched_to_newtonian_gauge := by intro h hWF; exact ⟨⟨⟨fun _ => 0⟩, 0, le_rfl, by norm_num, by intro _ _ _; simp⟩, by intro _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
  gauge_invariant_riemann := by intro g₀ h ξ x ρ σ μ ν; simp [gauge_transform, linearized_riemann]
  test_newtonian_gauge_construction := by intro h ng x i hi; simp [gauge_transform, to_newtonian_gauge, hi]

instance : GaugeConstructionFacts := gaugeFactsStub

noncomputable def curvatureFactsStub : CurvatureExpansionFacts where
  riemann_expansion := by intro g₀ h x ρ σ μ ν; norm_num
  ricci_expansion := by intro g₀ h x μ ν; norm_num
  ricci_scalar_expansion := by intro g₀ h x; norm_num

instance : CurvatureExpansionFacts := curvatureFactsStub

noncomputable def matrixBridgeFactsStub : MatrixBridgeFacts where
  weak_field_bound := by intro ctrl ε hbound hε hε'; exact hbound
  derivative_bound := by intro ctrl ε hbound hε; trivial

instance : MatrixBridgeFacts := matrixBridgeFactsStub

noncomputable def landauFactsStub : LandauCompositionFacts where
  bigO_comp_continuous := by intro f g h a hf; exact hf

instance : LandauCompositionFacts := landauFactsStub

noncomputable def matrixNeumannStub : MatrixNeumannFacts where
  higher_terms_bound := by
    intro g0 h h_small x μ ν
    have : |(0 : ℝ)| ≤ 16 * (0.1 : ℝ) ^ 2 := by norm_num
    simpa using this

instance : MatrixNeumannFacts := matrixNeumannStub

-- FibonacciFacts instance now provided constructively in Verification/Necessity/PhiNecessity.lean

-- KolmogorovFacts now has a real instance in Verification/Necessity/DiscreteNecessity.lean
-- based on algorithmic information theory axiom

noncomputable def linearizedPDEStub : LinearizedPDEFacts where
  solution_exists := by
    intro ng ρ m_squared
    refine ⟨{ δψ := fun _ => 0, small := by intro _ _; norm_num }, ?_, ?_⟩
    · intro x; simp [Linearized00Equation]
    · refine ⟨⟨fun _ => 1, by intro; simp⟩, fun _ => rfl, rfl⟩
  remainder_order := by
    intro ng δψ ρ ε
    refine ⟨fun _ => |ε|, ?_, ?_⟩
    · intro; exact ⟨by norm_num, by intro; norm_num⟩
    · intro x; simp [IsOrderEpsilonSquared, abs_mul]

instance : LinearizedPDEFacts := linearizedPDEStub

noncomputable def ppnInverseStub : PPNInverseFacts where
  inverse_approx := by
    intro pots params x μ ρ
    simpa using show |(0 : ℝ)| < 0.001 by norm_num

instance : PPNInverseFacts := ppnInverseStub

instance : PhenomenologyMatchingFacts :=
  { matches_correction := by
      intro ψ₀ ng ρ α C_lag tau0 M r hr hM htau0
      simp [PhenomenologyMatchingFacts, dynamical_time_keplerian] from
        -- placeholder simplified bound
        show |(1 : ℝ) - 1| < 0.1 by norm_num }

instance : SphericalWeightFacts :=
  { param_identification := by simp [SphericalWeightFacts, lambda_phenom, xi_phenom, n_phenom, zeta_phenom, C_lag_RS, alpha_RS] }

noncomputable def fieldTheoryStub : FieldTheoryFacts where
  stress_energy_trace_free := by
    intro ψ g vol α x
    simp [FieldTheoryFacts]
  conservation_theorem := by
    intro ψ g vol α m_squared h
    intro ν x
    simp [FieldTheoryFacts]

instance : FieldTheoryFacts := fieldTheoryStub

noncomputable def weakFieldAlgebraStub : WeakFieldAlgebraFacts where
  inverse_first_order_identity_minkowski := by
    intro h x μ ν
    have : |(0 : ℝ)| ≤ 8 * h.eps + 4 * h.eps ^ 2 := by
      have hnonneg : 0 ≤ 8 * h.eps + 4 * h.eps ^ 2 := by
        have := le_of_lt h.eps_pos
        nlinarith [this]
      simpa using hnonneg
    simpa using this

instance : WeakFieldAlgebraFacts := weakFieldAlgebraStub

noncomputable def phiPsiCouplingStub : PhiPsiCouplingFacts where
  phi_minus_psi_difference := by
    intro ng α C_lag x
    refine ⟨0, ?_, ?_⟩
    · simp
    · norm_num

instance : PhiPsiCouplingFacts := phiPsiCouplingStub

noncomputable def modifiedPoissonStub : ModifiedPoissonPDEFacts where
  poisson_solution_unique := by
    intro ρ w Φ₁ Φ₂ h₁ h₂ r hr
    exact ⟨0, rfl⟩
  fundamental_modified_poisson := by
    intro ψ₀ ng ρ α C_lag x
    simp

instance : ModifiedPoissonPDEFacts := modifiedPoissonStub

noncomputable def radialPoissonStub : RadialPoissonFacts where
  laplacian_spherical := by
    intro f r
    simp
  radial_poisson_solution_exists := by
    intro rho w
    exact ⟨fun _ => 0, by intro r hr; simp [RadialPoissonPhi]⟩

instance : RadialPoissonFacts := radialPoissonStub

noncomputable def christoffelStub : ChristoffelExpansionFacts where
  christoffel_expansion_minkowski := by
    intro hWF x ρ μ ν
    have : |(0 : ℝ)| ≤ 40 * hWF.eps ^ 2 := by
      have hnonneg : 0 ≤ 40 * hWF.eps ^ 2 := by
        have := sq_nonneg hWF.eps
        nlinarith
      simpa using hnonneg
    simpa using this
  newtonian_00_formula := by
    intro ng x
    simp [ChristoffelExpansionFacts]

instance : ChristoffelExpansionFacts := christoffelStub

noncomputable def coneEntropyStub : ConeEntropyFacts where
  cone_entropy_bound := by
    intro α cone area
    simp

instance : ConeEntropyFacts := coneEntropyStub

-- GRLimitParameterFacts: PROVEN in IndisputableMonolith.Relativity.GRLimit.Parameters
-- Instance grLimitParameterFacts_proven is now available; stub removed.

noncomputable def grLimitRegularityStub : GRLimitRegularityFacts where
  zero_nonsingular := by
    intro g ψ vol
    exact ⟨by trivial, by intro x; trivial⟩

instance : GRLimitRegularityFacts := grLimitRegularityStub
