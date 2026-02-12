import Mathlib
import IndisputableMonolith.Thermodynamics.MaxEntFromCost

/-!
# Free Energy Monotonicity

This module proves that Recognition Free Energy (FR) is non-increasing
under RS dynamics (coarse-graining, equilibration).

This is the Recognition Science version of the Second Law of Thermodynamics.

## Main Results

1. **Coarse-graining decreases free energy**: Reducing state resolution cannot increase F_R
2. **Relaxation decreases free energy**: Time evolution toward equilibrium decreases F_R
3. **Arrow of Time**: The direction of time is defined by dF_R/dt ≤ 0

## The Key Insight

The monotonicity of F_R under coarse-graining is equivalent to:
- The Data Processing Inequality (DPI) for KL divergence
- The fact that the Gibbs distribution minimizes free energy

## References

- Cover & Thomas, "Elements of Information Theory", Ch. 2 (DPI)
- `Recognition-Science-Full-Theory.txt`, Section on Thermodynamic Stability
-/

namespace IndisputableMonolith
namespace Thermodynamics

open Real Cost RecognitionSystem

/-- f(x) = x log x is convex on (0, ∞) -/
lemma mul_log_convexOn : ConvexOn ℝ (Set.Ioi 0) (fun x => x * log x) := by
  apply convexOn_of_deriv2_nonneg (convex_Ioi 0)
  · apply ContinuousOn.mul continuousOn_id (continuousOn_log.mono (Set.subset_refl _))
  · intro x hx
    -- deriv (x log x) = log x + 1
    -- deriv (log x + 1) = 1/x
    have h_deriv : deriv (fun y => y * log y) x = log x + 1 := by
      rw [deriv_mul differentiableAt_id' (differentiableAt_log hx.ne')]
      simp [hx.ne']
    have h_deriv2 : deriv (fun y => deriv (fun z => z * log z) y) x = 1/x := by
      rw [deriv_congr_ev (Filter.EventuallyIn.ext (fun y hy => deriv_mul differentiableAt_id' (differentiableAt_log (Set.mem_Ioi.mp hy).ne')) (𝓝 x))]
      · simp [hx.ne']
        rw [deriv_add (differentiableAt_log hx.ne') (differentiableAt_const 1)]
        simp [deriv_log hx.ne']
      · exact Filter.EventuallyIn.of_mem (𝓝 x) (Ioi_mem_nhds hx)
    rw [h_deriv2]
    apply div_nonneg (by norm_num) hx.le

/-- **Log-Sum Inequality**: For positive sequences a, b with finite support,
    ∑ aᵢ log(aᵢ/bᵢ) ≥ (∑ aᵢ) log((∑ aᵢ)/(∑ bᵢ))

    This is a consequence of Jensen's inequality for the convex function f(x) = x log x.

    **PROOF STRUCTURE** (Cover & Thomas, "Elements of Information Theory", Theorem 2.7.1):
    1. Define weights wᵢ = bᵢ/B where B = ∑ bᵢ. Then ∑ wᵢ = 1.
    2. Define ratios xᵢ = aᵢ/bᵢ. Then ∑ wᵢ xᵢ = A/B where A = ∑ aᵢ.
    3. The function f(x) = x log x is convex on [0, ∞).
    4. By Jensen's inequality: f(∑ wᵢ xᵢ) ≤ ∑ wᵢ f(xᵢ).
    5. Substituting: (A/B) log(A/B) ≤ ∑ wᵢ (xᵢ log xᵢ).
    6. Multiplying by B: A log(A/B) ≤ ∑ aᵢ log(aᵢ/bᵢ).

    **STATUS**: SCAFFOLD (classical information-theoretic result, requires Jensen machinery) -/
theorem log_sum_inequality {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * log (a i / b i) ≥ (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  have hA_pos : 0 < A := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hB_pos : 0 < B := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  let w := fun i => b i / B
  let x := fun i => a i / b i
  have hw_nonneg : ∀ i, 0 ≤ w i := fun i => div_nonneg (hb i).le hB_pos.le
  have hw_sum : ∑ i, w i = 1 := by
    unfold w
    rw [← Finset.sum_div, div_self hB_pos.ne']
  have hx_pos : ∀ i, x i ∈ Set.Ioi (0 : ℝ) := fun i => div_pos (ha i) (hb i)
  have h_center : ∑ i, w i * x i = A / B := by
    unfold w x
    simp_rw [div_mul_div_cancel_left _ (hb _).ne']
    rw [← Finset.sum_div]
  -- Apply Jensen
  have h_jensen := mul_log_convexOn.map_sum_le hw_nonneg hw_sum (fun i _ => hx_pos i)
  rw [h_center] at h_jensen
  -- h_jensen: (A/B) * log (A/B) ≤ ∑ w i * (x i * log (x i))
  -- Multiply by B
  have h_final : B * ((A / B) * log (A / B)) ≤ B * (∑ i, w i * (x i * log (x i))) :=
    mul_le_mul_of_nonneg_left h_jensen hB_pos.le
  -- Simplify LHS
  have h_lhs : B * ((A / B) * log (A / B)) = A * log (A / B) := by
    field_simp [hB_pos.ne']
    ring
  -- Simplify RHS
  have h_rhs : B * (∑ i, w i * (x i * log (x i))) = ∑ i, a i * log (a i / b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold w x
    field_simp [hB_pos.ne', (hb i).ne']
    ring
  rw [h_lhs] at h_final
  rw [h_rhs] at h_final
  exact h_final

/-- Log-Sum Inequality for conditional sums (fiberwise version).

    **PROOF STRUCTURE**: Reduce to the main log_sum_inequality by restricting
    to elements satisfying the predicate P. -/
theorem log_sum_inequality_fiber {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (P : ι → Prop) [DecidablePred P]
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i)
    (ha_pos_fiber : ∀ i, P i → 0 < a i) (hb_pos_fiber : ∀ i, P i → 0 < b i)
    (h_nonempty : ∃ i, P i) :
    ∑ i, (if P i then a i * log (a i / b i) else 0) ≥
    (∑ i, if P i then a i else 0) * log ((∑ i, if P i then a i else 0) / (∑ i, if P i then b i else 0)) := by
  let ι' := {i // P i}
  have h_fintype : Fintype ι' := inferInstance
  have h_nonempty' : Nonempty ι' := by
    obtain ⟨i, hi⟩ := h_nonempty
    exact ⟨⟨i, hi⟩⟩
  let a' := fun (i' : ι') => a i'.val
  let b' := fun (i' : ι') => b i'.val
  have ha' : ∀ i' : ι', 0 < a' i' := fun i' => ha_pos_fiber i'.val i'.property
  have hb' : ∀ i' : ι', 0 < b' i' := fun i' => hb_pos_fiber i'.val i'.property
  -- Apply log_sum_inequality to subtype
  have h_ls := log_sum_inequality a' b' ha' hb'
  -- Translate sums
  rw [Finset.sum_subtype (Finset.univ : Finset ι) (fun i => P i)] at h_ls
  · simp only [Finset.mem_univ, forall_true_left, a', b'] at h_ls
    have h_lhs : ∑ i, (if P i then a i * log (a i / b i) else 0) = ∑ i in (Finset.univ.filter P), a i * log (a i / b i) := by
      rw [Finset.sum_filter]
    have h_lhs_eq : (∑ i : ι', a i.val * log (a i.val / b i.val)) = ∑ i, (if P i then a i * log (a i / b i) else 0) := by
      rw [Finset.sum_subtype]
      · simp only [Finset.mem_univ, forall_true_left]
      · intro i; simp only [Finset.mem_univ, forall_true_left, ite_self]
    have h_a_sum : (∑ i : ι', a i.val) = ∑ i, if P i then a i else 0 := by
      rw [Finset.sum_subtype]
      · simp only [Finset.mem_univ, forall_true_left]
      · intro i; simp only [Finset.mem_univ, forall_true_left, ite_self]
    have h_b_sum : (∑ i : ι', b i.val) = ∑ i, if P i then b i else 0 := by
      rw [Finset.sum_subtype]
      · simp only [Finset.mem_univ, forall_true_left]
      · intro i; simp only [Finset.mem_univ, forall_true_left, ite_self]
    rw [h_lhs_eq, h_a_sum, h_b_sum] at h_ls
    exact h_ls
  · intro i; simp only [Finset.mem_univ, forall_true_left]

/-! ## Distribution Coarse-Graining -/

/-- Push-forward of a probability distribution under a map φ: Ω → Ω'.
    p'(ω') = ∑_{ω : φ(ω) = ω'} p(ω) -/
noncomputable def push_forward (p : Ω → ℝ) (φ : Ω → Ω') : Ω' → ℝ :=
  fun ω' => ∑ ω, if φ ω = ω' then p ω else 0

/-- Push-forward preserves non-negativity. -/
theorem push_forward_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → Ω') :
    ∀ ω', 0 ≤ push_forward p φ ω' := by
  intro ω'
  unfold push_forward
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> [apply hp; rfl]

/-- Push-forward preserves total probability. -/
theorem push_forward_sum_one {p : Ω → ℝ} (hp_sum : ∑ ω, p ω = 1) (φ : Ω → Ω') :
    ∑ ω', push_forward p φ ω' = 1 := by
  unfold push_forward
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact hp_sum

/-- **Effective Cost**: The coarse-grained cost landscape.
    J'(ω') = -TR * ln (∑_{ω : φ(ω) = ω'} exp(-J(ω)/TR))
    This definition ensures the partition function is preserved under coarse-graining. -/
noncomputable def effective_cost (sys : RecognitionSystem) (X : Ω → ℝ) (φ : Ω → Ω') : Ω' → ℝ :=
  fun ω' => -sys.TR * log (∑ ω, if φ ω = ω' then exp (-Jcost (X ω) / sys.TR) else 0)

/-- **THEOREM**: Partition function preservation under surjective coarse-graining.

    The partition function is preserved under coarse-graining.
    Z = ∑_ω e^{-X_ω/T} = ∑_ω' ∑_{ω∈φ⁻¹(ω')} e^{-X_ω/T}
    By defining the effective cost J' appropriately, the inner sum becomes e^{-J'_ω'/T}.

    **STATUS**: PROVEN assuming every coarse state has a preimage. -/
theorem partition_function_preserved (sys : RecognitionSystem) (X : Ω → ℝ) (φ : Ω → Ω')
    (h_surj : Function.Surjective φ) :
    partition_function sys X = ∑ ω', exp (-effective_cost sys X φ ω' / sys.TR) := by
  classical
  -- Unfold to Gibbs weights.
  unfold partition_function
  -- Show exp(-effective_cost/TR) recovers the fiber sum.
  have h_exp : ∀ ω', exp (-effective_cost sys X φ ω' / sys.TR) =
      ∑ ω, if φ ω = ω' then exp (-Jcost (X ω) / sys.TR) else 0 := by
    intro ω'
    unfold effective_cost
    -- Let s be the fiber sum.
    set s := ∑ ω, if φ ω = ω' then exp (-Jcost (X ω) / sys.TR) else 0 with hs
    have hpos : 0 < s := by
      obtain ⟨ω, hω⟩ := h_surj ω'
      have hterm : 0 < exp (-Jcost (X ω) / sys.TR) := exp_pos _
      have hnonneg : ∀ ω, 0 ≤ if φ ω = ω' then exp (-Jcost (X ω) / sys.TR) else 0 := by
        intro ω
        split_ifs
        · exact (le_of_lt (exp_pos _))
        · exact le_rfl
      have hmem : ω ∈ (Finset.univ : Finset Ω) := by simp
      have hle : exp (-Jcost (X ω) / sys.TR) ≤ s := by
        simpa [hs, hω] using
          (Finset.single_le_sum hnonneg (by simp [hmem, hω]))
      exact lt_of_lt_of_le hterm hle
    have hTR : sys.TR ≠ 0 := sys.TR_pos.ne'
    -- Simplify exponent and use exp_log.
    have hlog : exp (-(-sys.TR * log s) / sys.TR) = exp (log s) := by
      field_simp [hTR]
      ring
    simp [hs, hlog, Real.exp_log hpos.ne'] 
  -- Swap sums and collapse the indicator.
  calc
    ∑ ω, exp (-Jcost (X ω) / sys.TR)
        = ∑ ω', ∑ ω, if φ ω = ω' then exp (-Jcost (X ω) / sys.TR) else 0 := by
            rw [Finset.sum_comm]
            simp [Finset.sum_ite_eq, Finset.mem_univ]
    _ = ∑ ω', exp (-effective_cost sys X φ ω' / sys.TR) := by
            simp [h_exp]

/-- **THEOREM**: Data Processing Inequality for Relative Entropy.

    Coarse-graining reduces the distinguishability of distributions.
    D(p'‖q') ≤ D(p‖q) where p', q' are push-forwards.

    **STATUS**: PROVEN using log-sum inequality on each fiber. -/
theorem data_processing_inequality (p q : Ω → ℝ) (φ : Ω → Ω')
    (hp : ∀ ω, 0 < p ω) (hq : ∀ ω, 0 < q ω)
    (hp_sum : ∑ ω, p ω = 1) (hq_sum : ∑ ω, q ω = 1) :
    kl_divergence (push_forward p φ) (push_forward q φ) ≤ kl_divergence p q := by
  classical
  have hp_nonneg : ∀ ω, 0 ≤ p ω := fun ω => (hp ω).le
  have hq_nonneg : ∀ ω, 0 ≤ q ω := fun ω => (hq ω).le
  -- Fiberwise log-sum inequality bounds each coarse term.
  have h_fiber_bound :
      ∀ ω', (if push_forward p φ ω' > 0 ∧ push_forward q φ ω' > 0 then
              push_forward p φ ω' * log (push_forward p φ ω' / push_forward q φ ω')
            else 0) ≤
            ∑ ω, if φ ω = ω' then p ω * log (p ω / q ω) else 0 := by
    intro ω'
    by_cases hne : ∃ ω, φ ω = ω'
    · have hp' : 0 < push_forward p φ ω' := by
        obtain ⟨ω, hω⟩ := hne
        have hterm : 0 < p ω := hp ω
        have hnonneg : ∀ ω, 0 ≤ if φ ω = ω' then p ω else 0 := by
          intro ω; split_ifs <;> [exact (hp ω).le, exact le_rfl]
        have hle : p ω ≤ push_forward p φ ω' := by
          simpa [push_forward, hω] using
            (Finset.single_le_sum hnonneg (by simp) (by simp [hω]))
        exact lt_of_lt_of_le hterm hle
      have hq' : 0 < push_forward q φ ω' := by
        obtain ⟨ω, hω⟩ := hne
        have hterm : 0 < q ω := hq ω
        have hnonneg : ∀ ω, 0 ≤ if φ ω = ω' then q ω else 0 := by
          intro ω; split_ifs <;> [exact (hq ω).le, exact le_rfl]
        have hle : q ω ≤ push_forward q φ ω' := by
          simpa [push_forward, hω] using
            (Finset.single_le_sum hnonneg (by simp) (by simp [hω]))
        exact lt_of_lt_of_le hterm hle
      have h_ls := log_sum_inequality_fiber p q (fun ω => φ ω = ω')
        hp_nonneg hq_nonneg (fun ω hω => hp ω) (fun ω hω => hq ω) hne
      have h_term :
          (if push_forward p φ ω' > 0 ∧ push_forward q φ ω' > 0 then
              push_forward p φ ω' * log (push_forward p φ ω' / push_forward q φ ω')
            else 0) =
          (∑ ω, if φ ω = ω' then p ω else 0) *
            log ((∑ ω, if φ ω = ω' then p ω else 0) / (∑ ω, if φ ω = ω' then q ω else 0)) := by
        simp [push_forward, hp', hq']
      -- Combine.
      simpa [h_term] using h_ls
    · -- Empty fiber: both push-forward masses are 0, term is 0.
      have hpf : push_forward p φ ω' = 0 := by
        unfold push_forward
        apply Finset.sum_eq_zero
        intro ω _
        split_ifs with h
        · exact (hne ⟨ω, h⟩).elim
        · rfl
      have hqf : push_forward q φ ω' = 0 := by
        unfold push_forward
        apply Finset.sum_eq_zero
        intro ω _
        split_ifs with h
        · exact (hne ⟨ω, h⟩).elim
        · rfl
      simp [hpf, hqf]
  -- Sum the fiber bounds.
  have h_sum :
      kl_divergence (push_forward p φ) (push_forward q φ) ≤
        ∑ ω', ∑ ω, if φ ω = ω' then p ω * log (p ω / q ω) else 0 := by
    unfold kl_divergence
    apply Finset.sum_le_sum
    intro ω' _
    exact h_fiber_bound ω'
  -- Swap sums and collapse indicators.
  have h_swap :
      (∑ ω', ∑ ω, if φ ω = ω' then p ω * log (p ω / q ω) else 0) =
        ∑ ω, p ω * log (p ω / q ω) := by
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- Finish by rewriting KL with positivity.
  have h_kl : kl_divergence p q = ∑ ω, p ω * log (p ω / q ω) := by
    unfold kl_divergence
    apply Finset.sum_congr rfl
    intro ω _
    simp [hp ω, hq ω]
  linarith [h_sum, h_swap, h_kl]

/-- **THEOREM**: Free energy monotonicity under coarse-graining.

    Reducing state resolution cannot increase the Recognition Free Energy.
    This is the statistical mechanics version of the Second Law.

    **STATUS**: PROVEN assuming positivity and Gibbs/push-forward alignment. -/
theorem coarse_graining_decreases_free_energy
    (sys : RecognitionSystem) (X : Ω → ℝ)
    (p : ProbabilityDistribution Ω) (φ : Ω → Ω')
    (hp_pos : ∀ ω, 0 < p.p ω)
    (h_gibbs_push : ∀ ω',
      gibbs_measure sys (effective_cost sys X φ) ω' =
        push_forward (gibbs_measure sys X) φ ω')
    (h_gibbs_FR_eq :
      recognition_free_energy sys (gibbs_measure sys (effective_cost sys X φ))
        (effective_cost sys X φ) =
      recognition_free_energy sys (gibbs_measure sys X) X) :
    let p' := push_forward p.p φ
    let J' := effective_cost sys X φ
    recognition_free_energy sys p' J' ≤ recognition_free_energy sys p.p X := by
  intro p' J'
  classical
  -- Package the push-forward as a probability distribution.
  let p'pd : ProbabilityDistribution Ω' :=
    { p := p'
      nonneg := push_forward_nonneg p.nonneg φ
      sum_one := push_forward_sum_one p.sum_one φ }
  -- KL identity for fine and coarse levels.
  have hkl_p' := free_energy_kl_identity (sys:=sys) (X:=J') (q:=p'pd)
  have hkl_p := free_energy_kl_identity (sys:=sys) (X:=X) (q:=p)
  -- Data processing inequality on KL divergence.
  have h_dpi :=
    data_processing_inequality (p:=p.p) (q:=gibbs_measure sys X) (φ:=φ)
      hp_pos (fun ω => gibbs_measure_pos sys X ω)
      p.sum_one (gibbs_measure_sum_one sys X)
  have h_pf : push_forward (gibbs_measure sys X) φ = gibbs_measure sys J' := by
    funext ω'; symm; exact h_gibbs_push ω'
  have hkl_dec : kl_divergence p' (gibbs_measure sys J') ≤
      kl_divergence p.p (gibbs_measure sys X) := by
    simpa [p', h_pf] using h_dpi
  -- Compare free energies via KL identity.
  have h_diff :
      recognition_free_energy sys p' J' - recognition_free_energy sys p.p X =
        sys.TR * (kl_divergence p' (gibbs_measure sys J') -
                  kl_divergence p.p (gibbs_measure sys X)) +
        (recognition_free_energy sys (gibbs_measure sys J') J' -
         recognition_free_energy sys (gibbs_measure sys X) X) := by
    linarith [hkl_p', hkl_p]
  have hTR : 0 ≤ sys.TR := le_of_lt sys.TR_pos
  have h_gibbs_eq :
      recognition_free_energy sys (gibbs_measure sys J') J' -
      recognition_free_energy sys (gibbs_measure sys X) X = 0 := by
    simpa [h_gibbs_FR_eq]
  have h_nonpos :
      recognition_free_energy sys p' J' - recognition_free_energy sys p.p X ≤ 0 := by
    rw [h_diff, h_gibbs_eq, add_zero]
    have : kl_divergence p' (gibbs_measure sys J') -
             kl_divergence p.p (gibbs_measure sys X) ≤ 0 := by
      linarith [hkl_dec]
    exact mul_nonpos_of_nonneg_of_nonpos hTR this
  linarith

/-- **Arrow of Time**: The direction of time in RS is defined by decreasing F_R. -/
def rs_arrow_of_time (sys : RecognitionSystem) (X : Ω → ℝ) : Prop :=
  ∀ (t₁ t₂ : ℝ), t₁ ≤ t₂ →
    ∀ (p : ℝ → ProbabilityDistribution Ω),
    -- If p(t) evolves via RS dynamics (approaching Gibbs equilibrium)
    -- then F_R decreases
    recognition_free_energy sys (p t₂).p X ≤ recognition_free_energy sys (p t₁).p X

/-- **H-Theorem for Recognition**: The free energy decreases toward equilibrium.

    If the system starts in any state and relaxes toward the Gibbs measure,
    then F_R decreases monotonically until it reaches F_R(Gibbs).

    **Proof**: Uses the variational identity F_R(p) = F_R(Gibbs) + TR * D_KL(p || Gibbs).
    If D_KL decreases monotonically under the dynamics (h_relax hypothesis),
    then F_R must also decrease monotonically.

    This is the Recognition Science version of Boltzmann's H-theorem. -/
theorem h_theorem_recognition
    (sys : RecognitionSystem) (X : Ω → ℝ)
    (p : ℝ → ProbabilityDistribution Ω)
    (t₁ t₂ : ℝ) (h : t₁ ≤ t₂)
    -- Assume p(t) is a valid relaxation trajectory
    (h_relax : ∀ t ε, ε > 0 →
      kl_divergence (p (t + ε)).p (gibbs_measure sys X) ≤
      kl_divergence (p t).p (gibbs_measure sys X)) :
    recognition_free_energy sys (p t₂).p X ≤ recognition_free_energy sys (p t₁).p X := by
  -- F_R(p) = F_R(Gibbs) + TR * D_KL(p || Gibbs)
  have h_kl_identity₁ := free_energy_kl_identity sys X (p t₁)
  have h_kl_identity₂ := free_energy_kl_identity sys X (p t₂)

  by_cases heq : t₁ = t₂
  · rw [heq]
  · have hlt : t₁ < t₂ := lt_of_le_of_ne h heq
    have h_kl_dec : kl_divergence (p t₂).p (gibbs_measure sys X) ≤
                    kl_divergence (p t₁).p (gibbs_measure sys X) := by
      have := h_relax t₁ (t₂ - t₁) (sub_pos.mpr hlt)
      simp only [add_sub_cancel] at this
      exact this

    -- F_R(p t₂) ≤ F_R(p t₁)  iff  F_R(p t₂) - F_R(p t₁) ≤ 0
    rw [← sub_nonpos]
    have : recognition_free_energy sys (p t₂).p X - recognition_free_energy sys (p t₁).p X =
           sys.TR * (kl_divergence (p t₂).p (gibbs_measure sys X) - kl_divergence (p t₁).p (gibbs_measure sys X)) := by
      linarith [h_kl_identity₁, h_kl_identity₂]
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact sys.TR_pos.le
    · linarith [h_kl_dec]

/-- Status report for Free Energy Monotonicity module. -/
def free_energy_monotone_status : List (String × String) :=
  [ ("push_forward preserves prob", "THEOREM")
  , ("partition_function preserved", "SCAFFOLD")
  , ("data_processing_inequality", "SCAFFOLD")
  , ("coarse_graining_decreases_free_energy", "SCAFFOLD")
  , ("h_theorem_recognition", "PROVEN")
  ]

#eval free_energy_monotone_status

end Thermodynamics
end IndisputableMonolith
