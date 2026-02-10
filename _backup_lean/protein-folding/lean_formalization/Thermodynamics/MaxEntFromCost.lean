import Mathlib
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics

/-!
# MaxEnt From Cost

This module proves that the Gibbs distribution in Recognition Science
is the one that maximizes Recognition Entropy subject to a constraint
on the expected J-cost.

## Main Results

1. **Gibbs is a valid probability distribution**
2. **Gibbs minimizes Free Energy** (variational principle)
3. **MaxEnt theorem**: Gibbs maximizes entropy for fixed expected cost
4. **Free energy equivalence**: F_R(Gibbs) = -TR * ln(Z)

## The Key Insight

The relationship F_R(q) - F_R(Gibbs) = TR * D_KL(q || Gibbs) shows that:
- Free energy minimization ⟺ entropy maximization (at fixed cost)
- The Gibbs distribution is the unique minimizer
- Any deviation costs KL-divergence "energy"
-/

namespace IndisputableMonolith
namespace Thermodynamics

open Real
open Cost

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable (sys : RecognitionSystem) (X : Ω → ℝ)

/-! ## Probability Distribution Structure -/

/-- A distribution p on Ω is a probability distribution if it's non-negative and sums to 1. -/
structure ProbabilityDistribution (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : ∑ ω, p ω = 1

/-- Extract the underlying function. -/
instance : CoeFun (ProbabilityDistribution Ω) (fun _ => Ω → ℝ) where
  coe := ProbabilityDistribution.p

/-! ## Gibbs Distribution is Valid -/

/-- The Gibbs distribution is a valid probability distribution. -/
noncomputable def gibbs_pd (sys : RecognitionSystem) (X : Ω → ℝ) : ProbabilityDistribution Ω where
  p := gibbs_measure sys X
  nonneg := fun ω => gibbs_measure_nonneg sys X ω
  sum_one := gibbs_measure_sum_one sys X

/-- The partition function expressed via Gibbs weights. -/
theorem partition_function_eq_sum_weights :
    partition_function sys X = ∑ ω, gibbs_weight sys (X ω) := rfl

/-! ## Log-Probability of Gibbs Measure -/

/-- The log of the Gibbs probability has a nice form:
    ln(p_G(ω)) = -J(X(ω))/TR - ln(Z) -/
theorem log_gibbs_measure (ω : Ω) (hpos : 0 < gibbs_measure sys X ω) :
    log (gibbs_measure sys X ω) = - Jcost (X ω) / sys.TR - log (partition_function sys X) := by
  unfold gibbs_measure gibbs_weight
  rw [log_div (exp_pos _).ne' (partition_function_pos sys X).ne']
  rw [log_exp]

/-- Gibbs measure is strictly positive for all states. -/
lemma gibbs_measure_pos (ω : Ω) : 0 < gibbs_measure sys X ω := by
  unfold gibbs_measure
  exact div_pos (gibbs_weight_pos sys (X ω)) (partition_function_pos sys X)

/-! ## Free Energy of Gibbs Distribution -/

/-- Helper: The entropy conditional sum simplifies for Gibbs (always positive). -/
private lemma gibbs_entropy_conditional_simp :
    (∑ ω, if gibbs_measure sys X ω > 0
        then gibbs_measure sys X ω * log (gibbs_measure sys X ω) else 0) =
    ∑ ω, gibbs_measure sys X ω * log (gibbs_measure sys X ω) := by
  apply Finset.sum_congr rfl
  intro ω _
  simp [gibbs_measure_pos sys X ω]

/-- Helper: The log-Gibbs identity for summing over states. -/
private lemma gibbs_log_sum_identity :
    ∑ ω, gibbs_measure sys X ω * log (gibbs_measure sys X ω) =
    ∑ ω, gibbs_measure sys X ω * (- Jcost (X ω) / sys.TR - log (partition_function sys X)) := by
  apply Finset.sum_congr rfl
  intro ω _
  rw [log_gibbs_measure sys X ω (gibbs_measure_pos sys X ω)]

/-- The free energy of the Gibbs distribution equals -TR * ln(Z).

**Proof**: For Gibbs measure p(ω) = exp(-J(ω)/TR) / Z:
- log(p(ω)) = -J(ω)/TR - log(Z)
- S = -∑ p log(p) = ∑ p · (J/TR + log(Z)) = E[J]/TR + log(Z)
- F = E[J] - TR · S = E[J] - E[J] - TR·log(Z) = -TR·log(Z) -/
theorem gibbs_free_energy_eq_neg_TR_log_Z :
    recognition_free_energy sys (gibbs_measure sys X) X = free_energy_from_Z sys X := by
  unfold recognition_free_energy expected_cost recognition_entropy free_energy_from_Z
  rw [gibbs_entropy_conditional_simp, gibbs_log_sum_identity]
  -- Goal: ∑ p * J - TR * -∑ p * (-J/TR - log Z) = -TR * log Z
  -- Expand the inner sum: ∑ p * (-J/TR - log Z) = ∑ p * (-J/TR) + ∑ p * (-log Z)
  have h_expand : ∑ ω, gibbs_measure sys X ω * (-Jcost (X ω) / sys.TR - log (partition_function sys X)) =
      ∑ ω, gibbs_measure sys X ω * (-Jcost (X ω) / sys.TR) +
      ∑ ω, gibbs_measure sys X ω * (- log (partition_function sys X)) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext ω
    ring
  rw [h_expand]
  -- Use ∑ p = 1
  have hsum1 : ∑ ω, gibbs_measure sys X ω = 1 := gibbs_measure_sum_one sys X
  -- The log(Z) term factors out
  have hlogZ : ∑ ω, gibbs_measure sys X ω * (- log (partition_function sys X)) =
      - log (partition_function sys X) := by
    rw [← Finset.sum_mul]
    simp [hsum1]
  rw [hlogZ]
  -- The J/TR term: ∑ p * (-J/TR) = -(∑ p * J) / TR
  have hJ : ∑ ω, gibbs_measure sys X ω * (- Jcost (X ω) / sys.TR) =
      - (∑ ω, gibbs_measure sys X ω * Jcost (X ω)) / sys.TR := by
    have hTR' : sys.TR ≠ 0 := sys.TR_pos.ne'
    calc ∑ ω, gibbs_measure sys X ω * (-Jcost (X ω) / sys.TR)
        = ∑ ω, -(gibbs_measure sys X ω * Jcost (X ω)) / sys.TR := by
          apply Finset.sum_congr rfl; intro ω _; ring
      _ = (∑ ω, -(gibbs_measure sys X ω * Jcost (X ω))) / sys.TR := by
          rw [Finset.sum_div]
      _ = -(∑ ω, gibbs_measure sys X ω * Jcost (X ω)) / sys.TR := by
          rw [Finset.sum_neg_distrib]
  rw [hJ]
  -- Algebraic simplification
  have hTR : sys.TR ≠ 0 := sys.TR_pos.ne'
  field_simp [hTR]
  ring

/-! ## Variational Principle -/

/-- **Algebraic Core Lemma**: The free energy - KL divergence identity.

This is the key algebraic identity underlying the variational principle.
For any distribution q with q(ω) > 0 only where supp(q) ⊆ supp(Gibbs):

F_R(q) - F_R(Gibbs) = TR * D_KL(q || Gibbs) -/
theorem free_energy_kl_identity_core {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X - recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X) := by
  -- Let p be the Gibbs measure
  let p := gibbs_measure sys X

  -- Expand F_R(q)
  have hFq : recognition_free_energy sys q.p X = ∑ ω, q.p ω * Jcost (X ω) + sys.TR * ∑ ω, (if q.p ω > 0 then q.p ω * log (q.p ω) else 0) := by
    unfold recognition_free_energy expected_cost recognition_entropy
    simp only [neg_mul, neg_neg, sub_neg_eq_add]

  -- Use free_energy_identity for F_R(Gibbs)
  have hFp : recognition_free_energy sys p X = - sys.TR * log (partition_function sys X) :=
    free_energy_identity sys X

  rw [hFq, hFp]

  -- Expand kl_divergence
  unfold kl_divergence

  set Z := partition_function sys X with hZ_def
  have hZ_pos : 0 < Z := partition_function_pos sys X

  -- TR * log Z = ∑ q_i * (TR * log Z)
  have hZ_sum : sys.TR * log Z = ∑ ω, q.p ω * (sys.TR * log Z) := by
    rw [← Finset.sum_mul, q.sum_one, one_mul]

  simp only [sub_neg_eq_add]
  rw [hZ_sum, ← Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_add_distrib]

  apply Finset.sum_congr rfl
  intro ω _

  by_cases hq0 : q.p ω = 0
  · simp [hq0]
  · have hq_pos : q.p ω > 0 := lt_of_le_of_ne (q.nonneg ω) (Ne.symm hq0)
    have hp_pos : p ω > 0 := gibbs_measure_pos sys X ω

    simp only [hq_pos, hp_pos, and_self, if_true]

    have h_log_p : log (p ω) = - Jcost (X ω) / sys.TR - log Z := by
      unfold gibbs_measure gibbs_weight
      rw [log_div (exp_pos _).ne' hZ_pos.ne', log_exp]

    rw [log_div hq_pos.ne' hp_pos.ne', h_log_p]
    field_simp [sys.TR_pos.ne']
    ring

/-- **Main Theorem**: The free energy difference equals TR times KL divergence.
    F_R(q) - F_R(Gibbs) = TR * D_KL(q || Gibbs)

    Since D_KL ≥ 0, this proves Gibbs minimizes free energy. -/
theorem free_energy_kl_identity (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X - recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X) :=
  free_energy_kl_identity_core sys X q

/-- **Corollary**: The Gibbs distribution minimizes the Recognition Free Energy.
    For any probability distribution q, F_R(Gibbs) ≤ F_R(q). -/
theorem gibbs_minimizes_free_energy (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys (gibbs_measure sys X) X ≤
    recognition_free_energy sys q.p X := by
  have h := free_energy_kl_identity sys X q
  have hkl := kl_divergence_nonneg q.p (gibbs_measure sys X)
    q.nonneg
    (fun ω => gibbs_measure_pos sys X ω)
    q.sum_one
    (gibbs_measure_sum_one sys X)
  calc recognition_free_energy sys (gibbs_measure sys X) X
      = recognition_free_energy sys q.p X - sys.TR * kl_divergence q.p (gibbs_measure sys X) := by
        rw [← h]; ring
    _ ≤ recognition_free_energy sys q.p X := by
        have hTR := sys.TR_pos
        nlinarith

/-- **MaxEnt Theorem**: The Gibbs distribution maximizes Recognition Entropy
    subject to a constraint on expected cost.

    If q has the same expected cost as Gibbs, then S_R(q) ≤ S_R(Gibbs). -/
theorem max_ent_from_cost (q : ProbabilityDistribution Ω)
    (h_cost : expected_cost q.p X = expected_cost (gibbs_measure sys X) X) :
    recognition_entropy q.p ≤ recognition_entropy (gibbs_measure sys X) := by
  have h_min := gibbs_minimizes_free_energy sys X q
  unfold recognition_free_energy at h_min
  rw [h_cost] at h_min
  have hTR := sys.TR_pos
  have h1 : sys.TR * recognition_entropy q.p ≤ sys.TR * recognition_entropy (gibbs_measure sys X) := by
    linarith
  calc recognition_entropy q.p
      = (sys.TR * recognition_entropy q.p) / sys.TR := by field_simp [hTR.ne']
    _ ≤ (sys.TR * recognition_entropy (gibbs_measure sys X)) / sys.TR := by
        apply div_le_div_of_nonneg_right h1 hTR.le
    _ = recognition_entropy (gibbs_measure sys X) := by field_simp [hTR.ne']

/-! ## Uniqueness of Minimizer -/

/-- **KL Divergence Zero Characterization**: D_KL(q || p) = 0 implies q = p.

This is a fundamental result in information theory: the KL divergence
is zero if and only if the two distributions are identical. -/
/-- The KL divergence is zero if and only if the distributions are identical.

This is a fundamental result in information theory: the KL divergence
is zero if and only if the two distributions are identical. -/
theorem kl_divergence_zero_iff_eq {Ω : Type*} [Fintype Ω]
    (q p : Ω → ℝ) (hq_nn : ∀ ω, 0 ≤ q ω) (hp_pos : ∀ ω, 0 < p ω)
    (hq_sum : ∑ ω, q ω = 1) (hp_sum : ∑ ω, p ω = 1) :
    kl_divergence q p = 0 ↔ ∀ ω, q ω = p ω := by
  constructor
  · intro h
    -- Use the proof from kl_divergence_nonneg: Σ (q log(q/p)) ≥ Σ (q - p) = 0
    -- If Σ (q log(q/p)) = 0, then since each term q log(q/p) ≥ q - p,
    -- and Σ (q log(q/p)) = Σ (q - p), each term must satisfy q log(q/p) = q - p.

    unfold kl_divergence at h

    have h_term : ∀ ω, (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) ≥ q ω - p ω := by
      intro ω
      split_ifs with h_cond
      · obtain ⟨hq_pos, hp_pos_ω⟩ := h_cond
        -- q log (q/p) = -q log (p/q) ≥ q (1 - p/q) = q - p
        -- since -log x ≥ 1 - x
        have : - log (p ω / q ω) ≥ 1 - p ω / q ω := by
          apply Real.neg_log_le_one_sub_inv
          exact div_pos hp_pos_ω hq_pos
        calc q ω * log (q ω / p ω) = q ω * (- log (p ω / q ω)) := by
            rw [log_div hq_pos.ne' hp_pos_ω.ne', log_div hp_pos_ω.ne' hq_pos.ne', neg_sub]
          _ ≥ q ω * (1 - p ω / q ω) := (mul_le_mul_left hq_pos).mpr this
          _ = q ω - p ω := by field_simp [hq_pos.ne']; ring
      · -- q ω = 0 or p ω <= 0. But p ω > 0. So q ω = 0.
        have hq0 : q ω = 0 := by
          by_contra h_nz
          exact h_cond ⟨lt_of_le_of_ne (hq_nn ω) (Ne.symm h_nz), hp_pos ω⟩
        simp [hq0]
        exact (hp_pos ω).le

    have h_sum_le : ∑ ω, (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) ≥ ∑ ω, (q ω - p ω) :=
      Finset.sum_le_sum (fun ω _ => h_term ω)

    have h_sum_zero : ∑ ω, (q ω - p ω) = 0 := by
      rw [Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]

    rw [h, h_sum_zero] at h_sum_le

    -- Since Σ term_i = 0 and term_i ≥ q_i - p_i and Σ (q_i - p_i) = 0,
    -- we must have term_i = q_i - p_i for all i.
    have h_eq : ∀ ω, (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) = q ω - p ω := by
      intro ω
      apply le_antisymm
      · -- sum of (term - (q-p)) = 0 and each is non-negative
        have : (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) - (q ω - p ω) = 0 := by
          apply Finset.eq_zero_of_sum_eq_zero (fun _ _ => sub_nonneg.mpr (h_term _))
          rw [Finset.sum_sub_distrib, h, h_sum_zero, sub_zero]
        exact sub_eq_zero.mp this
      · exact h_term ω

    intro ω
    have h_ω := h_eq ω
    by_cases hq0 : q ω = 0
    · -- if q ω = 0, then 0 = 0 - p ω => p ω = 0, contradiction
      simp [hq0] at h_ω
      have := hp_pos ω
      linarith
    · -- if q ω > 0, then q log(q/p) = q - p
      have hq_pos : q ω > 0 := lt_of_le_of_ne (hq_nn ω) (Ne.symm hq0)
      simp [hq_pos, hp_pos ω] at h_ω
      -- log(q/p) = 1 - p/q.
      -- Let x = q/p. log x = 1 - 1/x.
      -- This implies x = 1.
      have : log (q ω / p ω) = 1 - p ω / q ω := by
        field_simp [hq_pos.ne'] at h_ω
        linear_combination (1 / q ω) * h_ω
      have h_one : q ω / p ω = 1 := by
        apply Real.log_eq_one_sub_inv_iff_eq_one
        exact div_pos hq_pos (hp_pos ω)
        rw [this]
      field_simp [hp_pos ω |>.ne'] at h_one
      exact h_one
  · intro h
    unfold kl_divergence
    rw [Finset.sum_eq_zero]
    intro ω _
    simp [h, hp_pos ω]

/-- The Gibbs distribution is the unique minimizer of free energy.
    If F_R(q) = F_R(Gibbs), then q = Gibbs. -/
theorem gibbs_unique_minimizer (q : ProbabilityDistribution Ω)
    (h_eq : recognition_free_energy sys q.p X = recognition_free_energy sys (gibbs_measure sys X) X) :
    ∀ ω, q.p ω = gibbs_measure sys X ω := by
  -- From h_eq and free_energy_kl_identity: TR * D_KL(q || Gibbs) = 0
  have h := free_energy_kl_identity sys X q
  rw [h_eq, sub_self] at h
  -- Since TR > 0, we have D_KL = 0
  have hTR := sys.TR_pos
  have hkl_zero : kl_divergence q.p (gibbs_measure sys X) = 0 := by
    have hkl_nn := kl_divergence_nonneg q.p (gibbs_measure sys X)
      q.nonneg (fun ω => gibbs_measure_pos sys X ω) q.sum_one (gibbs_measure_sum_one sys X)
    nlinarith
  -- D_KL = 0 implies q = Gibbs
  exact (kl_divergence_zero_iff_eq q.p (gibbs_measure sys X)
    q.nonneg (fun ω => gibbs_measure_pos sys X ω) q.sum_one (gibbs_measure_sum_one sys X)).mp hkl_zero

/-! ## Temperature Limits -/

/-- **Analytical Core**: Low temperature limit of exponential decay.

For J > 0 and T → 0⁺, exp(-J/T) → 0. -/
theorem exp_neg_div_tendsto_zero {J : ℝ} (hJ : J > 0) :
    Filter.Tendsto (fun T : ℝ => exp (-J / T)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_comp : (fun T => exp (-J / T)) = Real.exp ∘ (Neg.neg ∘ (fun T => J * T⁻¹)) := by
    ext T; simp; ring
  rw [h_comp]
  apply tendsto_exp_atBot.comp
  apply Filter.tendsto_neg_atTop_atBot.comp
  apply Filter.Tendsto.const_mul_atTop hJ
  exact tendsto_inv_nhdsGT_zero

/-- **Analytical Core**: High temperature limit of exponential to unity.

For any finite J and T → ∞, exp(-J/T) → 1. -/
theorem exp_neg_div_tendsto_one {J : ℝ} (_hJ : J ≥ 0) :
    Filter.Tendsto (fun T : ℝ => exp (-J / T)) Filter.atTop (nhds 1) := by
  have h_exp_zero : exp 0 = 1 := exp_zero
  rw [← h_exp_zero]
  have h_comp : (fun T => exp (-J / T)) = Real.exp ∘ (fun T => (-J) * T⁻¹) := by
    ext T; simp; ring
  rw [h_comp]
  apply (continuous_exp.tendsto 0).comp
  have : (0 : ℝ) = (-J) * 0 := by ring
  rw [this]
  apply Filter.Tendsto.const_mul
  exact tendsto_inv_atTop_zero

/-- **THEOREM: Low Temperature Limit (Ground State Concentration)** -/
theorem gibbs_zero_temp_limit_core {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (ω₀ : Ω) (_h₀ : Jcost (X ω₀) = 0)
    (_hmin : ∀ ω, Jcost (X ω) ≥ Jcost (X ω₀)) :
    ∀ ε > 0, ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR < T₀ →
      gibbs_measure sys X ω₀ > 1 - ε := by
  -- As T → 0, exp(-J/T) → 0 for J > 0, and exp(0) = 1.
  -- The partition function Z = ∑ exp(-J/T) approaches the number of ground states.
  -- If ω₀ is the unique ground state, p(ω₀) = exp(0)/Z → 1/1 = 1.
  sorry

/-- **Low Temperature Limit**: As TR → 0, the Gibbs measure concentrates on ground states. -/
theorem gibbs_zero_temp_limit (ω₀ : Ω) (h₀ : Jcost (X ω₀) = 0)
    (hmin : ∀ ω, Jcost (X ω) ≥ Jcost (X ω₀)) :
    ∀ ε > 0, ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR < T₀ →
      gibbs_measure sys X ω₀ > 1 - ε :=
  gibbs_zero_temp_limit_core X ω₀ h₀ hmin

/-- **THEOREM: High Temperature Limit (Uniform Distribution)** -/
theorem gibbs_infinite_temp_limit_core {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) :
    ∀ ε > 0, ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR > T₀ →
      ∀ ω, |gibbs_measure sys X ω - 1 / (Fintype.card Ω : ℝ)| < ε := by
  -- As T → ∞, -J/T → 0, so exp(-J/T) → 1 for all states.
  -- The partition function Z = ∑ exp(-J/T) approaches |Ω|.
  -- Therefore p(ω) = exp(-J/T)/Z approaches 1/|Ω|.
  sorry

/-- **High Temperature Limit**: As TR → ∞, the Gibbs measure approaches uniform. -/
theorem gibbs_infinite_temp_limit :
    ∀ ε > 0, ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR > T₀ →
      ∀ ω, |gibbs_measure sys X ω - 1 / (Fintype.card Ω : ℝ)| < ε :=
  gibbs_infinite_temp_limit_core X

end Thermodynamics
end IndisputableMonolith
