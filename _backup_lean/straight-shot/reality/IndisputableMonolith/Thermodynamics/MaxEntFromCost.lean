import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics

/-!
# Maximum Entropy from Cost Minimization

This module proves that the Gibbs distribution emerges from the principle of
maximum entropy subject to a cost constraint.
-/

namespace IndisputableMonolith
namespace Thermodynamics

open Real Cost RecognitionSystem

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable (sys : RecognitionSystem) (X : Ω → ℝ)

/-- **THEOREM: The Free Energy - KL Divergence Identity**
    F_R(q) - F_R(Gibbs) = TR * D_KL(q || Gibbs)

    **Proof**: F_R(q) = ⟨X⟩_q - TR*S(q) = ∑ q_ω X_ω + TR ∑ q_ω log q_ω
    For Gibbs: p_ω = exp(-X_ω/TR)/Z, so log p_ω = -X_ω/TR - log Z
    D_KL(q||p) = ∑ q_ω log(q_ω/p_ω) = ∑ q_ω log q_ω + ∑ q_ω (X_ω/TR + log Z)
               = -S(q)/TR + ⟨X⟩_q/TR + log Z
    TR * D_KL = -TR*S(q) + ⟨X⟩_q + TR*log Z = F_R(q) - (-TR*log Z) = F_R(q) - F_R(Gibbs) -/
theorem free_energy_kl_identity (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X - recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X) := by
  -- Use the fact that F_R(Gibbs) = -TR * log(Z) from free_energy_identity
  have h_gibbs_FR := free_energy_identity sys X
  rw [h_gibbs_FR]
  unfold recognition_free_energy expected_cost recognition_entropy free_energy_from_Z

  -- F_R(q) = ∑ q J - TR * (-∑ q log q) = ∑ q J + TR ∑ q log q
  -- D_KL(q||p) = ∑ q log(q/p) where p = gibbs
  -- TR * D_KL = TR ∑ q log q - TR ∑ q log p
  -- log p_ω = log(exp(-J_ω/TR)/Z) = -J_ω/TR - log Z
  -- TR ∑ q log p = TR ∑ q (-J_ω/TR - log Z) = -∑ q J - TR log Z ∑ q = -∑ q J - TR log Z
  -- TR * D_KL = TR ∑ q log q + ∑ q J + TR log Z
  -- F_R(q) - F_R(Gibbs) = (∑ q J + TR ∑ q log q) - (-TR log Z) = ∑ q J + TR ∑ q log q + TR log Z
  -- These match! QED.

  unfold kl_divergence gibbs_measure gibbs_weight partition_function
  set Z := ∑ ω, exp (-Jcost (X ω) / sys.TR) with hZ
  have hZ_pos : 0 < Z := by
    rw [hZ]; apply Finset.sum_pos (fun ω _ => exp_pos _) Finset.univ_nonempty

  -- Expand log(q/p) = log q - log p = log q - (-J/TR - log Z) = log q + J/TR + log Z
  have h_log_gibbs : ∀ ω, log (exp (-Jcost (X ω) / sys.TR) / Z) = -Jcost (X ω) / sys.TR - log Z := by
    intro ω
    rw [log_div (exp_pos _).ne' hZ_pos.ne', log_exp]

  -- The algebra after expansion: both sides should simplify to the same expression.
  -- LHS: recognition_free_energy sys q.p X - (-sys.TR * Real.log Z)
  --    = (∑ q J + TR ∑ q log q) + TR log Z
  -- RHS: TR * D_KL(q || Gibbs)
  --    = TR * ∑ q log(q/p) = TR ∑ q log q - TR ∑ q log p
  --    = TR ∑ q log q - TR ∑ q (-J/TR - log Z)
  --    = TR ∑ q log q + ∑ q J + TR log Z
  -- These are equal.
  simp only [sub_eq_add_neg, neg_neg, neg_mul, mul_neg, h_log_gibbs]
  rw [Finset.mul_sum, Finset.mul_sum]
  -- The goal reduces to showing the sums are equal after distribution.
  ring_nf
  -- Use the fact that ∑ q = 1 for probability distributions
  have hq_sum := q.sum_one
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1
  ext ω
  ring

/-- **THEOREM: Free Energy Minimization**
    The Gibbs distribution minimizes the Recognition Free Energy. -/
theorem gibbs_minimizes_free_energy_basic (p : ProbabilityDistribution Ω) :
    recognition_free_energy sys (gibbs_measure sys X) X ≤ recognition_free_energy sys p.p X := by
  have h := free_energy_kl_identity sys X p
  have hkl := kl_divergence_nonneg p.p (gibbs_measure sys X)
    p.nonneg
    (fun ω => gibbs_measure_pos sys X ω)
    p.sum_one
    (gibbs_measure_sum_one sys X)
  calc recognition_free_energy sys (gibbs_measure sys X) X
      = recognition_free_energy sys p.p X - sys.TR * kl_divergence p.p (gibbs_measure sys X) := by
        rw [← h]; ring
    _ ≤ recognition_free_energy sys p.p X := by
        have hTR := sys.TR_pos
        nlinarith

/-- **THEOREM: MaxEnt Subject to Cost**
    The Gibbs distribution has maximum entropy among all distributions with the same
    expected cost. -/
theorem max_ent_subject_to_cost (p : ProbabilityDistribution Ω)
    (h_cost : expected_cost p.p X = expected_cost (gibbs_measure sys X) X) :
    recognition_entropy p.p ≤ recognition_entropy (gibbs_measure sys X) := by
  have h_min := gibbs_minimizes_free_energy_basic sys X p
  unfold recognition_free_energy at h_min
  rw [h_cost] at h_min
  have hTR := sys.TR_pos
  -- expected_cost - TR * entropy_gibbs ≤ expected_cost - TR * entropy_p
  -- -TR * entropy_gibbs ≤ -TR * entropy_p
  -- TR * entropy_p ≤ TR * entropy_gibbs
  -- entropy_p ≤ entropy_gibbs
  nlinarith

/-- **THEOREM: KL Divergence Zero Characterization**
    D_KL(q || p) = 0 iff q = p.

    **Proof**: KL divergence is non-negative by Jensen's inequality applied to
    the convex function -log. It equals zero iff log(q/p) = 0 a.s., i.e., q = p. -/
theorem kl_divergence_zero_iff_eq {Ω : Type*} [Fintype Ω]
    (q p : Ω → ℝ) (hq_nn : ∀ ω, 0 ≤ q ω) (hp_pos : ∀ ω, 0 < p ω)
    (hq_sum : ∑ ω, q ω = 1) (hp_sum : ∑ ω, p ω = 1) :
    kl_divergence q p = 0 ↔ ∀ ω, q ω = p ω := by
  constructor
  · -- D_KL = 0 → q = p
    intro h_kl_zero ω
    unfold kl_divergence at h_kl_zero
    -- The KL divergence is a sum of non-negative terms.
    -- If the sum is 0, each term must be 0.
    -- Define the term function
    let term := fun ω' => if 0 < q ω' then q ω' * log (q ω' / p ω') else 0

    -- Each term is non-negative (by x log x ≥ x - 1 applied to q/p)
    have h_term_nn : ∀ ω', 0 ≤ term ω' := by
      intro ω'
      simp only [term]
      split_ifs with hq
      · -- q ω' > 0: use the fact that x log x ≥ x - 1 for x > 0
        have hp' := hp_pos ω'
        have hqp_pos : 0 < q ω' / p ω' := div_pos hq hp'
        -- q log(q/p) ≥ q - p when we use the log inequality
        -- Actually, for the term to be non-negative, we use that
        -- q log(q/p) ≥ q - p, and ∑(q - p) = 0.
        -- More directly: if q > 0 and q ≠ p, the term is strictly positive.
        -- If q = p, the term is 0.
        by_cases h_eq : q ω' = p ω'
        · simp [h_eq, div_self hp'.ne', log_one]
        · -- q ≠ p with q > 0: the term is strictly positive
          have hne : q ω' / p ω' ≠ 1 := by
            intro heq
            have : q ω' = p ω' := by field_simp at heq; linarith
            exact h_eq this
          have h_log_pos : 0 < |log (q ω' / p ω')| := abs_pos.mpr (log_ne_zero.mpr ⟨hqp_pos.ne', hne⟩)
          nlinarith [mul_pos hq (abs_pos.mp h_log_pos)]
      · simp

    -- The sum of non-negative terms is 0
    have h_sum_term : ∑ ω', term ω' = 0 := h_kl_zero

    -- Each term must be 0
    have h_each_zero : ∀ ω', term ω' = 0 :=
      Finset.sum_eq_zero_iff_of_nonneg (fun ω' _ => h_term_nn ω') |>.mp h_sum_term

    -- For our specific ω
    specialize h_each_zero ω (Finset.mem_univ ω)
    simp only [term] at h_each_zero
    split_ifs at h_each_zero with hq
    · -- q ω > 0: log(q/p) = 0 means q = p
      have hp' := hp_pos ω
      have hqp_pos : 0 < q ω / p ω := div_pos hq hp'
      have h_mul_zero := h_each_zero
      have h_log_zero : log (q ω / p ω) = 0 := by
        by_contra h_ne
        have : q ω * log (q ω / p ω) ≠ 0 := mul_ne_zero hq.ne' h_ne
        exact this h_mul_zero
      rw [log_eq_zero] at h_log_zero
      rcases h_log_zero with h1 | h2 | h3
      · -- q/p = 1
        field_simp at h1
        linarith
      · -- q/p = 0: contradicts q > 0
        have : q ω = 0 := by field_simp at h2; linarith
        linarith
      · -- q/p = -1: contradicts q/p > 0
        linarith
    · -- q ω = 0: need to show p ω = 0, but p > 0, so need contradiction
      push_neg at hq
      have hq' := hq_nn ω
      interval_cases h : q ω
      -- Since ∑ q = 1 and ∑ p = 1 with p > 0, if q ω = 0 for all ω, sum would be 0 ≠ 1
      -- We need a different approach: use that if q ω = 0 < p ω, some other q ω' > p ω'
      -- But those terms would be strictly positive, contradicting D_KL = 0.
      -- Actually, let's use that the sum ∑ q = 1 = ∑ p, so if q ω = 0 < p ω,
      -- there must exist ω' with q ω' > p ω' (by pigeonhole).
      -- At that ω', the term q log(q/p) > 0, so D_KL > 0, contradiction.
      have hq_zero : q ω = 0 := le_antisymm hq hq'
      -- If q ω = 0 but p ω > 0, the sums can't both be 1 unless compensated.
      -- We use the contrapositive: D_KL = 0 forces q = p everywhere.
      -- For ω where q = 0 and p > 0, we'd need extra mass elsewhere in q.
      -- That extra mass creates strictly positive KL terms.
      exfalso
      -- Find an ω' where q ω' > p ω'
      have h_sum_diff : ∑ ω', (q ω' - p ω') = 0 := by simp [hq_sum, hp_sum]
      have h_this_neg : q ω - p ω < 0 := by linarith [hp_pos ω]
      -- Since sum of differences is 0 and this term is negative,
      -- there exists a term that is positive
      have h_exists_pos : ∃ ω' ∈ Finset.univ, q ω' - p ω' > 0 := by
        by_contra h_all_nonpos
        push_neg at h_all_nonpos
        have h_sum_nonpos : ∑ ω', (q ω' - p ω') ≤ ∑ ω', (0 : ℝ) := by
          apply Finset.sum_le_sum
          intro ω' _
          exact h_all_nonpos ω' (Finset.mem_univ ω')
        simp at h_sum_nonpos
        have h_strict : ∑ ω', (q ω' - p ω') < 0 := by
          calc ∑ ω', (q ω' - p ω') < (q ω - p ω) + ∑ ω' ∈ Finset.univ.erase ω, 0 := by
                simp only [Finset.sum_const_zero, add_zero]
                calc ∑ ω', (q ω' - p ω')
                    = (q ω - p ω) + ∑ ω' ∈ Finset.univ.erase ω, (q ω' - p ω') := by
                      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω)]
                  _ ≤ (q ω - p ω) + ∑ ω' ∈ Finset.univ.erase ω, 0 := by
                      apply add_le_add_left
                      apply Finset.sum_le_sum
                      intro ω' hω'
                      exact h_all_nonpos ω' (Finset.mem_univ ω')
                  _ = q ω - p ω := by simp
                  _ < 0 := h_this_neg
            _ = q ω - p ω := by simp
        linarith
      obtain ⟨ω', _, hω'_pos⟩ := h_exists_pos
      -- At ω', we have q ω' > p ω' > 0, so q ω' > 0 and q ω'/p ω' > 1
      have hq'_pos : 0 < q ω' := by linarith [hq_nn ω', hp_pos ω']
      have hp'_pos := hp_pos ω'
      have hqp_gt_1 : q ω' / p ω' > 1 := by
        rw [div_gt_one hp'_pos]
        linarith
      -- So log(q/p) > 0 and the term q log(q/p) > 0
      have h_log_pos : 0 < log (q ω' / p ω') := log_pos hqp_gt_1
      have h_term_pos : 0 < term ω' := by
        simp only [term]
        rw [if_pos hq'_pos]
        exact mul_pos hq'_pos h_log_pos
      -- But we proved all terms are 0
      have h_term_zero := h_each_zero
      -- Wait, h_each_zero is for ω, not ω'. Let me use the general fact.
      have h_all_zero := Finset.sum_eq_zero_iff_of_nonneg (fun ω' _ => h_term_nn ω') |>.mp h_sum_term
      have h_this_zero := h_all_zero ω' (Finset.mem_univ ω')
      linarith
  · -- q = p → D_KL = 0: direct computation
    intro h_eq
    unfold kl_divergence
    apply Finset.sum_eq_zero
    intro ω _
    simp only [h_eq ω, div_self (ne_of_gt (hp_pos ω)), log_one, mul_zero]
    split_ifs <;> rfl

/-- The Gibbs distribution is the unique minimizer of free energy. -/
theorem gibbs_unique_minimizer (q : ProbabilityDistribution Ω)
    (h_eq : recognition_free_energy sys q.p X = recognition_free_energy sys (gibbs_measure sys X) X) :
    ∀ ω, q.p ω = gibbs_measure sys X ω := by
  have h := free_energy_kl_identity sys X q
  rw [h_eq, sub_self] at h
  have hTR := sys.TR_pos
  have hkl_zero : kl_divergence q.p (gibbs_measure sys X) = 0 := by
    rw [eq_comm] at h
    have := mul_eq_zero.mp h
    cases this with
    | inl hTR0 => linarith
    | inr hkl0 => exact hkl0
  apply (kl_divergence_zero_iff_eq q.p (gibbs_measure sys X) q.nonneg (fun ω => gibbs_measure_pos sys X ω) q.sum_one (gibbs_measure_sum_one sys X)).mp
  exact hkl_zero

end Thermodynamics
end IndisputableMonolith
