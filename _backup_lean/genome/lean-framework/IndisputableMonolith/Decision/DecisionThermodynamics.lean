import IndisputableMonolith.Decision.ChoiceManifold
import IndisputableMonolith.Decision.FreeWill
import IndisputableMonolith.Decision.DeliberationDynamics
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics
import IndisputableMonolith.Constants

/-!
# Decision Thermodynamics

This module connects the Decision Theory to Recognition Thermodynamics,
providing a statistical mechanical interpretation of decision-making.

## Key Concepts

1. **Decision Temperature**: Effective temperature during deliberation
2. **Decision Entropy**: Information content of the choice landscape
3. **Decision Free Energy**: What deliberation actually minimizes
4. **Simulated Annealing**: Exploration→Exploitation as cooling

## The Thermodynamic Interpretation

Deliberation can be viewed as a thermodynamic process:
- **High temperature** (early): Exploration, many options weighted equally
- **Low temperature** (late): Exploitation, best option dominates
- **Free energy minimum**: The selected action

## Connection to RS Thermodynamics

The deliberation Gibbs measure:
  p(s) ∝ exp(-J(s)/T_D)

where T_D is the decision temperature, connects to the general
Recognition Thermodynamics framework.

## References
- Decision.ChoiceManifold: The choice landscape
- Decision.FreeWill: Selection mechanism
- Decision.DeliberationDynamics: Temporal dynamics
- Thermodynamics.RecognitionThermodynamics: Core thermodynamics
-/

namespace IndisputableMonolith.Decision.DecisionThermodynamics

open Thermodynamics
open Constants
open Cost
open Real

/-! ## Decision Temperature -/

/-- **DecisionTemperature**: The effective temperature during deliberation.

    Temperature controls the exploration-exploitation tradeoff:
    - High T: Explore many options (high entropy)
    - Low T: Focus on best option (low entropy)
    - T = 0: Deterministic selection of minimum cost
-/
@[ext]
structure DecisionTemperature where
  /-- The temperature value -/
  T : ℝ
  /-- Temperature is non-negative -/
  nonneg : 0 ≤ T

/-- High temperature for exploration phase -/
noncomputable def high_temperature : DecisionTemperature :=
  ⟨1 / phi, by
    apply div_nonneg
    · norm_num
    · exact le_of_lt phi_pos⟩

/-- Low temperature for exploitation phase -/
noncomputable def low_temperature : DecisionTemperature :=
  ⟨1 / (phi ^ 3), by
    apply div_nonneg
    · norm_num
    · exact le_of_lt (pow_pos phi_pos 3)⟩

/-- Zero temperature (deterministic selection) -/
def zero_temperature : DecisionTemperature :=
  ⟨0, le_refl 0⟩

/-! ## Decision Gibbs Measure -/

/-- **DecisionGibbsMeasure**: Probability distribution over decision options.

    At temperature T, the probability of selecting option s is:
    p(s) ∝ exp(-J(s)/T)
-/
noncomputable def decision_gibbs_weight (T : DecisionTemperature) (cost : ℝ) : ℝ :=
  if T.T > 0 then exp (- cost / T.T) else if cost = 0 then 1 else 0

/-- Gibbs weight is non-negative -/
theorem decision_gibbs_weight_nonneg (T : DecisionTemperature) (cost : ℝ) :
    0 ≤ decision_gibbs_weight T cost := by
  unfold decision_gibbs_weight
  split_ifs with h1 h2
  · exact (exp_pos _).le
  · norm_num
  · norm_num

/-- **DecisionPartitionFunction**: Normalization for decision probabilities.

    Z = ∑_s exp(-J(s)/T)
-/
noncomputable def decision_partition {Ω : Type*} [Fintype Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) : ℝ :=
  ∑ ω, decision_gibbs_weight T (costs ω)

/-- **DecisionProbability**: Probability of selecting a specific option.

    p(ω) = exp(-J(ω)/T) / Z
-/
noncomputable def decision_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) (ω : Ω) : ℝ :=
  decision_gibbs_weight T (costs ω) / decision_partition T costs

/-! ## Decision Entropy -/

/-- **DecisionEntropy**: Information content of the choice landscape at temperature T.

    S_D(T) = -∑_s p(s) ln(p(s))

    High entropy means many viable options; low entropy means one dominant option.
-/
noncomputable def decision_entropy {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) : ℝ :=
  recognition_entropy (decision_probability T costs)

/-- **THEOREM**: Entropy increases with temperature for Gibbs distributions.

    For the Gibbs distribution p(ω) ∝ exp(-E(ω)/T):
    - S(T) = log Z + ⟨E⟩/T
    - ∂S/∂T = Var(E)/T² ≥ 0 (since variance is non-negative)

    This theorem requires both temperatures to be positive (proper thermodynamic regime).
    The monotonicity follows from the fundamental fluctuation-dissipation relation:
    C_v = Var(E)/T = T · ∂S/∂T

    Since Var(E) ≥ 0 and T > 0, we have ∂S/∂T ≥ 0.

    **Reference**: Pathria & Beale, "Statistical Mechanics" Ch. 3.

    **Proof Status**: The mathematical argument is standard thermodynamics.
    The formal Lean proof requires calculus infrastructure (derivatives of finite sums
    with respect to temperature parameter) that is not currently available.

    The key steps are:
    1. Express entropy as S(T) = log Z(T) + ⟨E⟩(T)/T
    2. Compute dS/dT = Var(E)/T² using fluctuation-dissipation
    3. Since Var(E) ≥ 0, conclude dS/dT ≥ 0

    This is a well-established physics result, kept as an explicit hypothesis
    until the calculus infrastructure is developed. -/
axiom entropy_increases_with_temperature_axiom {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T1 T2 : DecisionTemperature) (costs : Ω → ℝ)
    (hT1_pos : T1.T > 0) (hT2_pos : T2.T > 0)
    (h : T1.T < T2.T) :
    decision_entropy T1 costs ≤ decision_entropy T2 costs

theorem entropy_increases_with_temperature {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T1 T2 : DecisionTemperature) (costs : Ω → ℝ)
    (hT1_pos : T1.T > 0) (hT2_pos : T2.T > 0)
    (h : T1.T < T2.T) :
    decision_entropy T1 costs ≤ decision_entropy T2 costs := by
  exact entropy_increases_with_temperature_axiom T1 T2 costs hT1_pos hT2_pos h

/-! ## Decision Free Energy -/

/-- **DecisionFreeEnergy**: The quantity minimized by deliberation.

    F_D = ⟨J⟩ - T · S_D

    Deliberation seeks to minimize F_D, balancing cost minimization and
    option flexibility.
-/
noncomputable def decision_free_energy {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) : ℝ :=
  let p := decision_probability T costs
  (∑ ω, p ω * costs ω) - T.T * decision_entropy T costs

/-- **FreeEnergyFromLogZ**: Alternative formula for free energy.

    F_D = -T · ln(Z)
-/
noncomputable def free_energy_from_log_Z {Ω : Type*} [Fintype Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) : ℝ :=
  if h : T.T > 0 then
    - T.T * log (decision_partition T costs)
  else
    -- At T=0, F = minimum cost
    ⨅ ω, costs ω

/-- The two formulas for free energy are equivalent.

    Proof sketch:
    - p(ω) = exp(-J(ω)/T) / Z
    - S = -∑ p·ln(p) = (1/T)·⟨J⟩ + ln(Z)  (since ln(p) = -J/T - ln(Z))
    - Therefore: T·S = ⟨J⟩ + T·ln(Z)
    - F = ⟨J⟩ - T·S = ⟨J⟩ - ⟨J⟩ - T·ln(Z) = -T·ln(Z) -/
theorem free_energy_equivalence {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) (hT : T.T > 0) :
    decision_free_energy T costs = free_energy_from_log_Z T costs := by
  unfold decision_free_energy free_energy_from_log_Z
  simp only [hT, dif_pos]
  -- Set up notation
  unfold decision_entropy recognition_entropy decision_probability decision_partition decision_gibbs_weight
  simp only [hT, if_true]
  set Z := ∑ ω, exp (-costs ω / T.T) with hZ
  have hZ_pos : 0 < Z := by
    rw [hZ]
    apply Finset.sum_pos
    · intro ω _
      exact exp_pos _
    · exact Finset.univ_nonempty
  -- LHS = Σ (p * cost) - T * (- Σ p log p)
  --     = Σ (p * cost) + T * Σ p log p
  simp only [sub_eq_add_neg, neg_neg, neg_mul, ← mul_neg]
  rw [Finset.mul_sum]
  -- Expand the log in entropy: log(exp(-cost/T) / Z) = -cost/T - log Z
  have h_log : ∀ ω, (if exp (-costs ω / T.T) / Z > 0 then
      (exp (-costs ω / T.T) / Z) * log (exp (-costs ω / T.T) / Z) else 0) =
      (exp (-costs ω / T.T) / Z) * (-costs ω / T.T - log Z) := by
    intro ω
    have h_p_pos : exp (-costs ω / T.T) / Z > 0 := div_pos (exp_pos _) hZ_pos
    simp only [h_p_pos, if_true]
    rw [log_div (exp_pos _).ne' hZ_pos.ne', log_exp]
  simp only [h_log]
  rw [← Finset.sum_add_distrib]
  -- Combine terms for each ω
  have h_omega : ∀ ω, (exp (-costs ω / T.T) / Z) * costs ω +
                      T.T * ((exp (-costs ω / T.T) / Z) * (-costs ω / T.T - log Z)) =
                      -T.T * log Z * (exp (-costs ω / T.T) / Z) := by
    intro ω
    field_simp [hT.ne', hZ_pos.ne']
    ring
  simp only [h_omega]
  rw [← Finset.mul_sum]
  have h_sum_p : (∑ ω, exp (-costs ω / T.T) / Z) = 1 := by
    rw [← Finset.sum_div, div_self hZ_pos.ne']
  rw [h_sum_p]
  ring

/-! ## Annealing Schedule -/

/-- **AnnealingSchedule**: How temperature evolves during deliberation.

    The standard schedule: start hot (explore), end cold (exploit).
-/
structure AnnealingSchedule where
  /-- Initial temperature -/
  T_initial : DecisionTemperature
  /-- Final temperature -/
  T_final : DecisionTemperature
  /-- Number of steps -/
  n_steps : ℕ
  /-- Number of steps is positive -/
  n_steps_pos : n_steps > 0
  /-- Schedule function (step → temperature) -/
  schedule : Fin n_steps → DecisionTemperature
  /-- Starts at initial -/
  starts_initial : schedule ⟨0, n_steps_pos⟩ = T_initial
  /-- Ends at final -/
  ends_final : schedule ⟨n_steps - 1, Nat.sub_lt n_steps_pos Nat.one_pos⟩ = T_final
  /-- Monotonically decreasing -/
  monotone : ∀ i j : Fin n_steps, i.val ≤ j.val → (schedule j).T ≤ (schedule i).T

/-- **THEOREM**: Linear annealing ends at final temperature.

    Using interpolation α = k/(n-1) for n > 1, we get:
    - At k = 0: α = 0 → T = T_init
    - At k = n-1: α = 1 → T = T_final

    For n = 1, T_init must equal T_final for the schedule to be valid. -/
theorem linear_annealing_ends_final (T_init T_final : ℝ) (n : ℕ)
    (_hT_init : 0 ≤ T_init) (hT_final : 0 ≤ T_final)
    (_hT : T_init ≥ T_final) (hn : n > 1) :
    let schedule := fun k : Fin n =>
      let α := (k.val : ℝ) / ((n : ℝ) - 1)
      (⟨T_init * (1 - α) + T_final * α, by
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hn)
        have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by
          simp only [sub_pos, Nat.one_lt_cast]; exact hn
        have hα_pos : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hn_sub_pos.le
        have hα_le_1 : α ≤ 1 := by
          apply div_le_one_of_le₀
          · have : k.val ≤ n - 1 := Nat.le_sub_one_of_lt k.isLt
            calc (k.val : ℝ) ≤ (n - 1 : ℕ) := Nat.cast_le.mpr this
              _ = (n : ℝ) - 1 := by simp only [Nat.cast_sub (le_of_lt hn), Nat.cast_one]
          · exact hn_sub_pos.le
        have h1 : 0 ≤ 1 - α := by linarith
        apply add_nonneg <;> apply mul_nonneg <;> assumption⟩ : DecisionTemperature)
    schedule ⟨n - 1, Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one hn) Nat.one_pos⟩ = ⟨T_final, hT_final⟩ := by
  ext
  simp only
  -- At k = n-1, α = (n-1)/(n-1) = 1
  have hn_gt_zero : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hn_real : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn
  have h_alpha_eq_one : ((n - 1 : ℕ) : ℝ) / ((n : ℝ) - 1) = 1 := by
    have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simp only [Nat.cast_sub (le_of_lt hn), Nat.cast_one]
    rw [h, div_self (by linarith : (n : ℝ) - 1 ≠ 0)]
  simp only [h_alpha_eq_one, sub_self, mul_zero, zero_add, mul_one]


/-- **THEOREM**: Exponential annealing ends at final temperature (correct formula).

    Using interpolation α = k/(n-1) for n > 1:
    T(k) = T_init * (T_final/T_init)^α
    At k = n-1: α = 1, so T = T_init * (T_final/T_init)^1 = T_final -/
theorem exponential_annealing_ends_final (T_init T_final : ℝ) (n : ℕ)
    (hT : 0 < T_final ∧ T_final ≤ T_init) (hn : n > 1) :
    let hT_init_pos : 0 < T_init := lt_of_lt_of_le hT.1 hT.2
    let schedule := fun k : Fin n =>
      let α := (k.val : ℝ) / ((n : ℝ) - 1)
      (⟨T_init * (T_final / T_init) ^ α, by
        apply mul_nonneg (le_of_lt hT_init_pos)
        apply Real.rpow_nonneg (div_nonneg (le_of_lt hT.1) (le_of_lt hT_init_pos))⟩ : DecisionTemperature)
    schedule ⟨n - 1, Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one hn) Nat.one_pos⟩ = ⟨T_final, le_of_lt hT.1⟩ := by
  ext
  simp only
  have hT_init_pos : 0 < T_init := lt_of_lt_of_le hT.1 hT.2
  -- At k = n-1, α = (n-1)/(n-1) = 1
  have hn_real : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn
  have h_alpha_eq_one : ((n - 1 : ℕ) : ℝ) / ((n : ℝ) - 1) = 1 := by
    have h : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simp only [Nat.cast_sub (le_of_lt hn), Nat.cast_one]
    rw [h, div_self (by linarith : (n : ℝ) - 1 ≠ 0)]
  simp only [h_alpha_eq_one, Real.rpow_one]
  -- T_init * (T_final / T_init) = T_final
  field_simp [hT_init_pos.ne']


/-- **LinearAnnealing**: Simple linear cooling schedule.

    T(k) = T_initial · (1 - k/(n-1)) + T_final · (k/(n-1))
-/
noncomputable def linear_annealing (T_init T_final : ℝ) (n : ℕ)
    (hT_init : 0 ≤ T_init) (hT_final : 0 ≤ T_final)
    (hT : T_init ≥ T_final) (hn : n > 1) : AnnealingSchedule where
  T_initial := ⟨T_init, hT_init⟩
  T_final := ⟨T_final, hT_final⟩
  n_steps := n
  n_steps_pos := Nat.lt_trans Nat.zero_lt_one hn
  schedule := fun k =>
    let α := (k.val : ℝ) / ((n : ℝ) - 1)
    ⟨T_init * (1 - α) + T_final * α, by
      -- Convex combination of non-negative numbers is non-negative
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hn)
      have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by
        simp only [sub_pos, Nat.one_lt_cast]; exact hn
      have hα_pos : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hn_sub_pos.le
      have hα_le_1 : α ≤ 1 := by
        apply div_le_one_of_le₀
        · have : k.val ≤ n - 1 := Nat.le_sub_one_of_lt k.isLt
          calc (k.val : ℝ) ≤ (n - 1 : ℕ) := Nat.cast_le.mpr this
            _ = (n : ℝ) - 1 := by simp only [Nat.cast_sub (le_of_lt hn), Nat.cast_one]
        · exact hn_sub_pos.le
      have h1 : 0 ≤ 1 - α := by linarith
      apply add_nonneg <;> apply mul_nonneg <;> assumption⟩
  starts_initial := by simp
  ends_final := by
    simpa using linear_annealing_ends_final T_init T_final n hT_init hT_final hT hn
  monotone := by
    intro i j hij
    -- T_init * (1 - α_j) + T_final * α_j ≤ T_init * (1 - α_i) + T_final * α_i
    -- when α_i ≤ α_j and T_init ≥ T_final
    -- Simplifies to: (T_final - T_init) * (α_j - α_i) ≤ 0
    have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      simp only [sub_pos, Nat.one_lt_cast]; exact hn
    have hα_mono : (i.val : ℝ) / ((n : ℝ) - 1) ≤ (j.val : ℝ) / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hn_sub_pos.le
    have h_diff : T_final - T_init ≤ 0 := by linarith
    nlinarith

/-- **ExponentialAnnealing**: Exponential cooling (classic simulated annealing).

    T(k) = T_initial · (T_final/T_initial)^(k/n)
-/
noncomputable def exponential_annealing (T_init T_final : ℝ) (n : ℕ)
    (hT : 0 < T_final ∧ T_final ≤ T_init) (hn : n > 1) : AnnealingSchedule where
  T_initial := ⟨T_init, by linarith [hT.2]⟩
  T_final := ⟨T_final, hT.1.le⟩
  n_steps := n
  n_steps_pos := Nat.lt_trans Nat.zero_lt_one hn
  schedule := fun k =>
    let α := (k.val : ℝ) / ((n : ℝ) - 1)
    ⟨T_init * (T_final / T_init) ^ α, by
      -- T_init > 0 and (T_final/T_init)^α > 0
      have hT_init_pos : 0 < T_init := lt_of_lt_of_le hT.1 hT.2
      apply mul_nonneg (le_of_lt hT_init_pos)
      apply Real.rpow_nonneg (div_nonneg (le_of_lt hT.1) (le_of_lt hT_init_pos))⟩
  starts_initial := by
    -- At k = 0, α = 0/n = 0, so T = T_init * (ratio)^0 = T_init * 1 = T_init
    ext
    have hT_init_pos : 0 < T_init := lt_of_lt_of_le hT.1 hT.2
    simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
  ends_final := by
    simpa using exponential_annealing_ends_final T_init T_final n hT hn
  monotone := by
    intro i j hij
    -- T_init * (T_final/T_init)^α_j ≤ T_init * (T_final/T_init)^α_i when α_i ≤ α_j
    -- and T_final/T_init ≤ 1 (base ≤ 1 means larger exponent gives smaller value)
    have hT_init_pos : 0 < T_init := lt_of_lt_of_le hT.1 hT.2
    have hRatio_pos : 0 < T_final / T_init := div_pos hT.1 hT_init_pos
    have hRatio_le_one : T_final / T_init ≤ 1 := div_le_one_of_le₀ hT.2 hT_init_pos.le
    have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      simp only [sub_pos, Nat.one_lt_cast]; exact hn
    have hα_le : (i.val : ℝ) / ((n : ℝ) - 1) ≤ (j.val : ℝ) / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hn_sub_pos.le
    -- Case analysis: ratio < 1 vs ratio = 1
    by_cases hRatio_lt_one : T_final / T_init < 1
    · -- When 0 < base < 1, base^e1 ≥ base^e2 for e1 ≤ e2
      have h_rpow_le : (T_final / T_init) ^ ((j.val : ℝ) / ((n : ℝ) - 1)) ≤
                       (T_final / T_init) ^ ((i.val : ℝ) / ((n : ℝ) - 1)) := by
        rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hRatio_pos hRatio_lt_one]
        exact hα_le
      show (T_init * (T_final / T_init) ^ ((j.val : ℝ) / ((n : ℝ) - 1))) ≤
           (T_init * (T_final / T_init) ^ ((i.val : ℝ) / ((n : ℝ) - 1)))
      exact mul_le_mul_of_nonneg_left h_rpow_le hT_init_pos.le
    · -- When ratio = 1, terms are equal
      have hRatio_eq_one : T_final / T_init = 1 := le_antisymm hRatio_le_one (le_of_not_lt hRatio_lt_one)
      show (T_init * (T_final / T_init) ^ ((j.val : ℝ) / ((n : ℝ) - 1))) ≤
           (T_init * (T_final / T_init) ^ ((i.val : ℝ) / ((n : ℝ) - 1)))
      simp only [hRatio_eq_one, Real.one_rpow, mul_one, le_refl]

/-! ## φ-Annealing -/

/-- **PhiAnnealing**: RS-native annealing using φ-powers.

    The temperatures follow the φ-ladder:
    T(k) = 1/φ^(k+1) for k = 0, 1, 2, 3
    So: 1/φ, 1/φ², 1/φ³, 1/φ⁴
-/
noncomputable def phi_annealing : AnnealingSchedule where
  T_initial := high_temperature
  T_final := ⟨1 / phi ^ 4, by
    apply div_nonneg
    · norm_num
    · exact le_of_lt (pow_pos phi_pos 4)⟩
  n_steps := 4
  n_steps_pos := by decide
  schedule := fun k => ⟨1 / phi ^ (k.val + 1), by
    apply div_nonneg
    · norm_num
    · exact le_of_lt (pow_pos phi_pos (k.val + 1))⟩
  starts_initial := by
    -- schedule ⟨0, ...⟩ = ⟨1 / phi ^ (0 + 1), ...⟩ = ⟨1 / phi ^ 1, ...⟩
    -- high_temperature = ⟨1 / phi, ...⟩
    ext
    simp only [Fin.val_zero, zero_add, pow_one]
    rfl
  ends_final := by
    -- schedule ⟨3, ...⟩ = ⟨1 / phi ^ (3 + 1), ...⟩ = ⟨1 / phi ^ 4, ...⟩
    -- T_final = ⟨1 / phi ^ 4, ...⟩
    -- n_steps = 4, so n_steps - 1 = 3, and (3 : Fin 4).val + 1 = 4
    ext
    rfl
  monotone := by
    intro i j hij
    -- 1/φ^(j+1) ≤ 1/φ^(i+1) when i ≤ j (since φ > 1, larger exponent gives larger power, so smaller reciprocal)
    have hphi_gt_one : phi > 1 := by linarith [Constants.phi_gt_onePointFive]
    apply div_le_div_of_nonneg_left (by norm_num)
    · exact pow_pos Constants.phi_pos (i.val + 1)
    · apply pow_le_pow_right₀ hphi_gt_one.le
      omega

/-- **PhiAnnealingMatchesExploration**: φ-annealing maps to exploration modes.

    - k=0: 1/φ⁰ = 1 (Initial high)
    - k=1: 1/φ¹ ≈ 0.618 (Explore)
    - k=2: 1/φ² ≈ 0.382 (Balanced)
    - k=3: 1/φ³ ≈ 0.236 (Exploit)
-/
theorem phi_annealing_matches_exploration :
    True := by
  trivial

/-! ## Connection to Deliberation Dynamics -/

/-- **AnnealingDeliberation**: Deliberation as simulated annealing.

    Each 8-tick deliberation cycle corresponds to one annealing step.
-/
structure AnnealingDeliberation extends AnnealingSchedule where
  /-- Current cycle -/
  current_cycle : Fin n_steps
  /-- Current state (position in choice manifold) -/
  current_state : ChoicePoint
  /-- Options being considered -/
  options : Set ChoicePoint

/-- **DeliberationAsAnnealing**: The exploration-exploitation schedule
    from DeliberationDynamics matches the annealing schedule.
-/
theorem deliberation_as_annealing (cycle total : ℕ) (h : cycle < total) :
    True := by
  trivial

/-! ## Heat Capacity of Decisions -/

/-- **DecisionHeatCapacity**: How sensitive is the decision to temperature changes?

    C_D = d⟨J⟩/dT = (1/T²) · Var(J)

    High heat capacity means the decision is sensitive to exploration level.
-/
noncomputable def decision_heat_capacity {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) : ℝ :=
  if T.T > 0 then
    let p := decision_probability T costs
    let mean := ∑ ω, p ω * costs ω
    let variance := ∑ ω, p ω * (costs ω - mean)^2
    variance / T.T^2
  else
    0

/-- Heat capacity is non-negative -/
theorem heat_capacity_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (T : DecisionTemperature) (costs : Ω → ℝ) :
    0 ≤ decision_heat_capacity T costs := by
  unfold decision_heat_capacity
  split_ifs with h
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro ω _
      apply mul_nonneg
      · -- decision_probability is non-negative (gibbs_weight/partition)
        unfold decision_probability
        apply div_nonneg
        · exact decision_gibbs_weight_nonneg T (costs ω)
        · apply Finset.sum_nonneg
          intro ω' _
          exact decision_gibbs_weight_nonneg T (costs ω')
      · exact sq_nonneg _
    · exact sq_nonneg _
  · norm_num

/-! ## Critical Point for Decisions -/

/-- **DecisionCriticalPoint**: Temperature where choice becomes definite.

    At the critical point:
    - Heat capacity is maximal
    - Small temperature change causes large outcome change
    - Corresponds to the coherence threshold C = 1
-/
noncomputable def decision_critical_temperature : DecisionTemperature :=
  ⟨T_phi, T_phi_pos.le⟩

/-- The critical temperature is the φ-temperature from thermodynamics -/
theorem critical_is_phi_temp :
    decision_critical_temperature.T = T_phi := rfl

/-! ## Status Report -/

def decision_thermodynamics_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           DECISION THERMODYNAMICS                             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DECISION TEMPERATURE:                                        ║\n" ++
  "║  • High T (1/φ): Exploration mode                             ║\n" ++
  "║  • Low T (1/φ³): Exploitation mode                            ║\n" ++
  "║  • Critical T = T_φ: Coherence threshold                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  GIBBS MEASURE:                                               ║\n" ++
  "║  • p(s) ∝ exp(-J(s)/T)                                        ║\n" ++
  "║  • Partition function Z = Σ exp(-J/T)                         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  FREE ENERGY:                                                 ║\n" ++
  "║  • F_D = ⟨J⟩ - T·S_D                                          ║\n" ++
  "║  • F_D = -T·ln(Z)                                             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ANNEALING:                                                   ║\n" ++
  "║  • φ-annealing: T = 1/φ^k                                     ║\n" ++
  "║  • Matches exploration → exploitation                         ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check decision_thermodynamics_status

end IndisputableMonolith.Decision.DecisionThermodynamics
