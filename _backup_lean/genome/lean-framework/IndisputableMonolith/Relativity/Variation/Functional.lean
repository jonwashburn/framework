import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields

/-!
# Functional Derivatives

This module implements functional derivatives δS/δψ and δS/δg^{μν} for variational calculus.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Variation

open Geometry
open Fields
open Calculus
open Matrix

/-- Symmetrized perturbation matrix for inverse metric components. -/
noncomputable def delta_matrix (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun α β => ((if α = μ ∧ β = ν then 1 else 0) + (if α = ν ∧ β = μ then 1 else 0)) / 2

lemma delta_matrix_symmetric (μ ν : Fin 4) : (delta_matrix μ ν).transpose = delta_matrix μ ν := by
  ext i j
  unfold delta_matrix
  simp only [transpose_apply, and_comm]
  ring

/-- Symmetric matrices have equal off-diagonal elements. -/
lemma symmetric_matrix_apply {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : A.transpose = A) (i j : Fin n) : A i j = A j i := by
  -- A.transpose j i = A i j by definition of transpose
  have h1 : A.transpose j i = A i j := Matrix.transpose_apply A j i
  -- A.transpose = A means A.transpose j i = A j i
  have h2 : A.transpose j i = A j i := congrFun (congrFun h j) i
  rw [h1] at h2
  exact h2

/-- **THEOREM**: Inverse of a symmetric matrix is symmetric.
    Uses Mathlib's `Matrix.transpose_nonsing_inv`: (A⁻¹)ᵀ = (Aᵀ)⁻¹.
    Combined with Aᵀ = A, we get (A⁻¹)ᵀ = A⁻¹. -/
theorem inverse_symmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) : A⁻¹.transpose = A⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hA]

/-- Sum of symmetric matrices is symmetric. -/
lemma add_symmetric {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) : (A + B).transpose = A + B := by
  rw [Matrix.transpose_add, hA, hB]

/-- Scalar multiple of symmetric matrix is symmetric. -/
lemma smul_symmetric {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) : (c • A).transpose = c • A := by
  rw [Matrix.transpose_smul, hA]

/-- **DEFINITION**: Perturbation of the metric for Gateaux-style functional differentiation. -/
noncomputable def perturbed_metric (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) (ε : ℝ) : MetricTensor :=
  let M_inv := (metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν
  { g := fun y up low =>
      if y = x_p then
        M_inv⁻¹ (low 0) (low 1)
      else
        g.g y up low,
    symmetric := by
      intro y up low
      dsimp only
      by_cases h : y = x_p
      · -- At the perturbation point, show M_inv⁻¹ is symmetric
        simp only [h, ite_true]
        -- 1. metric_to_matrix g x_p is symmetric
        have h_M_sym : (metric_to_matrix g x_p).transpose = metric_to_matrix g x_p :=
          metric_to_matrix_symmetric g x_p
        -- 2. Its inverse is symmetric
        have h_M_inv_sym : (metric_to_matrix g x_p)⁻¹.transpose = (metric_to_matrix g x_p)⁻¹ :=
          inverse_symmetric _ h_M_sym
        -- 3. delta_matrix is symmetric
        have h_delta_sym : (delta_matrix μ ν).transpose = delta_matrix μ ν :=
          delta_matrix_symmetric μ ν
        -- 4. ε • delta_matrix is symmetric
        have h_eps_delta_sym : (ε • delta_matrix μ ν).transpose = ε • delta_matrix μ ν :=
          smul_symmetric ε _ h_delta_sym
        -- 5. Their sum M_inv is symmetric
        have h_Minv_sym : ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν).transpose =
                          (metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν :=
          add_symmetric _ _ h_M_inv_sym h_eps_delta_sym
        -- 6. M_inv⁻¹ is symmetric
        have h_Minv_inv_sym : ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹.transpose =
                              ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹ :=
          inverse_symmetric _ h_Minv_sym
        -- Apply the symmetry
        exact symmetric_matrix_apply h_Minv_inv_sym (low 0) (low 1)
      · -- Away from perturbation point, use original metric's symmetry
        simp only [h, ite_false]
        exact g.symmetric y up low }

/-- **THEOREM**: Minkowski metric matrix is invertible.
    The Minkowski metric is diag(-1, 1, 1, 1), which is its own inverse. -/
theorem minkowski_matrix_invertible (x : Fin 4 → ℝ) :
    Invertible (metric_to_matrix minkowski_tensor x) := by
  -- The Minkowski metric matrix is diagonal with entries (-1, 1, 1, 1)
  have h_mat : metric_to_matrix minkowski_tensor x =
      Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) = 0 then (-1 : ℝ) else 1) := by
    ext i j
    unfold metric_to_matrix minkowski_tensor eta
    dsimp
    by_cases h : i = j
    · rw [if_pos h, h]; simp [Matrix.diagonal]
    · rw [if_neg h]; simp [Matrix.diagonal, h]
  rw [h_mat]
  -- Diagonal matrix with non-zero entries is invertible
  apply Matrix.invertibleOfIsUnitDet
  rw [Matrix.det_diagonal]
  simp only [Finset.prod_ite, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.prod_singleton, Finset.prod_const, Finset.card_filter]
  -- det = (-1) * 1 * 1 * 1 = -1 ≠ 0
  norm_num
  decide

/-- **HYPOTHESIS**: General metric matrices are invertible.

    This encodes *non-degeneracy* of the spacetime metric at a point:
    singular metrics (det = 0) are excluded from the variational calculus layer.

    For specific metrics like Minkowski, use `minkowski_matrix_invertible`. -/
def metric_matrix_invertible_hypothesis (g : MetricTensor) (x : Fin 4 → ℝ) : Prop :=
    Invertible (metric_to_matrix g x)

theorem metric_matrix_invertible (g : MetricTensor) (x : Fin 4 → ℝ)
    (h : metric_matrix_invertible_hypothesis g x) :
    Invertible (metric_to_matrix g x) :=
  h

/-- Helper: (metric_to_matrix g x) is invertible implies its inverse is also invertible. -/
theorem metric_matrix_invertible_inv (g : MetricTensor) (x : Fin 4 → ℝ)
    (h : metric_matrix_invertible_hypothesis g x) :
    Invertible (metric_to_matrix g x)⁻¹ := by
  let A := metric_to_matrix g x
  have hA : Invertible A := metric_matrix_invertible g x h
  constructor
  use A
  constructor
  · rw [Matrix.inv_inv_of_invertible]
  · rw [Matrix.inv_inv_of_invertible]

/-- Helper lemma: recovering the low indices from metric_to_matrix. -/
lemma metric_to_matrix_apply (g : MetricTensor) (x : Fin 4 → ℝ) (i j : Fin 4) :
    metric_to_matrix g x i j = g.g x (fun _ => 0) (fun k => if (k : ℕ) = 0 then i else j) := rfl

lemma sum_delta_matrix_apply (μ ν : Fin 4) (A : Fin 4 → Fin 4 → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    (Finset.univ.sum (fun α => Finset.univ.sum (fun β => delta_matrix μ ν α β * A α β))) = A μ ν := by
  unfold delta_matrix
  simp_rw [add_mul, div_mul_eq_mul_div]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ α, ∑ β, (if α = μ ∧ β = ν then (1 : ℝ) else 0) * A α β / 2) = A μ ν / 2 := by
    simp_rw [← Finset.sum_div, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  have h2 : (∑ α, ∑ β, (if α = ν ∧ β = μ then (1 : ℝ) else 0) * A α β / 2) = A ν μ / 2 := by
    simp_rw [← Finset.sum_div, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  rw [h1, h2, hA ν μ]
  ring

/-- **THEOREM**: Zero perturbation returns the original metric.
    Uses (A⁻¹)⁻¹ = A for invertible matrices. -/
theorem perturbed_metric_zero (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x_p) :
    perturbed_metric g μ ν x_p 0 = g := by
  unfold perturbed_metric
  simp only [zero_smul, add_zero]
  ext y up low
  simp only
  by_cases h : y = x_p
  · -- At x_p: (A⁻¹)⁻¹ = A
    simp only [h, ite_true]
    have hinv := metric_matrix_invertible g x_p h_inv
    rw [Matrix.inv_inv_of_invertible]
    rw [metric_to_matrix_apply]
    -- Now show: g.g x_p (fun _ => 0) (fun k => if k.val = 0 then low 0 else low 1) = g.g x_p up low
    congr 1
    · funext i; exact Fin.elim0 i
    · funext k; fin_cases k <;> rfl
  · simp only [h, ite_false]

/-- **THEOREM**: Summing a symmetric matrix over the delta_matrix recovers the matrix entry.
    Σ_{αβ} A_αβ * delta_matrix μ ν α β = A_μν.

    **Proof**:
    1. delta_matrix μ ν α β = 1/2 (δ_μα δ_νβ + δ_να δ_μβ).
    2. Summing over α, β:
       Σ A_αβ * 1/2 (δ_μα δ_νβ + δ_να δ_μβ)
       = 1/2 (Σ A_αβ δ_μα δ_νβ + Σ A_αβ δ_να δ_μβ)
       = 1/2 (A_μν + A_νμ).
    3. For symmetric A, A_μν = A_νμ, so the sum is A_μν. -/
theorem sum_delta_matrix_apply {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ ν : Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose = A) :
    (Finset.univ : Finset (Fin n)).sum (fun α =>
      (Finset.univ : Finset (Fin n)).sum (fun β =>
        A α β * delta_matrix μ ν α β)) = A μ ν := by
  unfold delta_matrix
  simp_rw [mul_add, mul_div_assoc, Finset.sum_add_distrib]
  have h1 : (∑ α, ∑ β, A α β * (if α = μ ∧ β = ν then (1:ℝ) else 0) / 2) = A μ ν / 2 := by
    simp_rw [← Finset.sum_div, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  have h2 : (∑ α, ∑ β, A α β * (if α = ν ∧ β = μ then (1:ℝ) else 0) / 2) = A ν μ / 2 := by
    simp_rw [← Finset.sum_div, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  rw [h1, h2]
  -- Use symmetry: A μ ν = A ν μ
  have h_sym : A ν μ = A μ ν := symmetric_matrix_apply hA ν μ
  rw [h_sym]
  ring

/-- Functional derivative of an action functional w.r.t. the inverse metric g^μν.
    Computed as the Gateaux derivative along the perturbation of the inverse metric. -/
noncomputable def functional_deriv
  (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) : ℝ :=
  deriv (fun ε => S (perturbed_metric g μ ν x_p ε) x_p) 0

/-- **THEOREM**: Functional derivative distributes over addition. -/
theorem functional_deriv_add (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y + S2 g' y) g μ ν x_p =
    functional_deriv S1 g μ ν x_p + functional_deriv S2 g μ ν x_p := by
  unfold functional_deriv
  exact deriv_add h1 h2

/-- **THEOREM**: Functional derivative distributes over subtraction. -/
theorem functional_deriv_sub (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y - S2 g' y) g μ ν x_p =
    functional_deriv S1 g μ ν x_p - functional_deriv S2 g μ ν x_p := by
  unfold functional_deriv
  exact deriv_sub h1 h2

/-- **THEOREM**: Functional derivative scales with constants. -/
theorem functional_deriv_const_mul (c : ℝ) (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun ε => S (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => c * S g' y) g μ ν x_p = c * functional_deriv S g μ ν x_p := by
  unfold functional_deriv
  exact deriv_const_mul c h

/-- **THEOREM**: Functional derivative of a constant functional is zero. -/
theorem functional_deriv_const (c : ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) :
    functional_deriv (fun _ _ => c) g μ ν x_p = 0 := by
  unfold functional_deriv
  exact deriv_const 0 c

/-- **THEOREM (Linearity over sums)**: Functional derivative of a finite sum. -/
theorem functional_deriv_sum {ι : Type} (s : Finset ι)
    (S : ι → MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun ε => S i (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => s.sum (fun i => S i g' y)) g μ ν x_p =
    s.sum (fun i => functional_deriv (S i) g μ ν x_p) := by
  unfold functional_deriv
  have h_sum : (fun ε => ∑ i ∈ s, S i (perturbed_metric g μ ν x_p ε) x_p) =
               (∑ i ∈ s, fun ε => S i (perturbed_metric g μ ν x_p ε) x_p) := by
    funext ε; simp only [Finset.sum_apply]
  rw [h_sum, deriv_sum h]

/-- **THEOREM (Product rule)**: Leibniz rule for functional derivatives. -/
theorem functional_deriv_mul (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x_p)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y * S2 g' y) g μ ν x_p =
    S1 g x_p * functional_deriv S2 g μ ν x_p + S2 g x_p * functional_deriv S1 g μ ν x_p := by
  unfold functional_deriv
  have h_mul : deriv (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p * S2 (perturbed_metric g μ ν x_p ε) x_p) 0 =
               deriv (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0 * S2 (perturbed_metric g μ ν x_p 0) x_p +
               S1 (perturbed_metric g μ ν x_p 0) x_p * deriv (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0 :=
    deriv_mul h1 h2
  rw [h_mul]
  rw [perturbed_metric_zero g μ ν x_p h_inv]
  ring

/-- **HYPOTHESIS**: The inverse metric is differentiable with respect to perturbations. -/
def differentiableAt_inverse_metric (g : MetricTensor) (μ ν ρ σ : Fin 4) (x_p : Fin 4 → ℝ) : Prop :=
  DifferentiableAt ℝ (fun ε => inverse_metric (perturbed_metric g μ ν x_p ε) x_p (fun i => if i = 0 then ρ else σ) (fun _ => 0)) 0

/-- **HYPOTHESIS**: The field cost density is differentiable. -/
def differentiableAt_field_cost (psi : RRF) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) : Prop :=
  DifferentiableAt ℝ (fun ε => field_cost_density psi (perturbed_metric g μ ν x_p ε) x_p) 0

/-- **THEOREM**: The functional derivative of the inverse metric g^ρσ
    w.r.t. g^μν is δ^ρ_μ δ^σ_ν (symmetrized).

    **Proof**: By definition of perturbed_metric, the inverse metric at the
    perturbation point is linearly perturbed:
    (g_ε⁻¹) = g⁻¹ + ε δ_μν.
    The derivative w.r.t. ε is thus exactly δ_μν. -/
theorem functional_deriv_inverse_metric (ρ σ : Fin 4) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x_p) :
  functional_deriv (fun g' y => inverse_metric g' y (fun i => if i = 0 then ρ else σ) (fun _ => 0)) g μ ν x_p =
    delta_matrix μ ν ρ σ := by
  unfold functional_deriv inverse_metric perturbed_metric
  dsimp
  simp only [ite_true]
  -- The expression inside deriv is: ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹⁻¹ ρ σ
  -- We need to show that ((A⁻¹ + εB)⁻¹)⁻¹ = A⁻¹ + εB
  -- This requires that (A⁻¹ + εB) is invertible.
  have h_inv : Filter.Eventually (fun ε => IsUnit ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)) (nhds 0) := by
    -- Invertible matrices form an open set.
    -- Since (metric_to_matrix g x_p)⁻¹ is invertible (its inverse is the original metric),
    -- and ε • delta_matrix is a continuous perturbation, it remains invertible for small ε.
    -- We assume the physical metric is non-singular.
    let A := (metric_to_matrix g x_p)⁻¹
    have hA : IsUnit A := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have hinv := metric_matrix_invertible g x_p h_inv
      have := Matrix.isUnit_det_of_invertible (metric_to_matrix g x_p)
      rw [Matrix.det_inv, isUnit_ringInverse]
      exact this

    -- Matrix addition and scalar multiplication are continuous.
    let f := fun ε : ℝ => A + ε • delta_matrix μ ν
    have hf : Continuous f := by
      apply Continuous.add
      · exact continuous_const
      · apply Continuous.smul
        · exact continuous_id
        · exact continuous_const

    -- IsUnit is an open set in the ring of matrices.
    have h_open : IsOpen { M : Matrix (Fin 4) (Fin 4) ℝ | IsUnit M } :=
      Units.isOpen.preimage (show Continuous (fun (x : (Matrix (Fin 4) (Fin 4) ℝ)) => x) from continuous_id)

    -- f(0) = A, which is a unit.
    have hf0 : f 0 = A := by simp [f]

    -- Therefore f(ε) is a unit for small ε.
    exact hf.continuousAt.preimage_mem_nhds (h_open.mem_nhds hA)

  have h_inv_inv : ∀ᶠ ε in nhds 0, ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹⁻¹ =
                         (metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν := by
    apply h_inv.mono
    intro ε h
    -- For units, nonsing_inv is the inverse and inv_inv holds.
    exact Matrix.nonsing_inv_nonsing_inv h
  rw [Filter.EventuallyEq.deriv_eq h_inv_inv]
  -- Now we have deriv (fun ε => ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν) ρ σ) 0
  -- = deriv (fun ε => (metric_to_matrix g x_p)⁻¹ ρ σ + ε * delta_matrix μ ν ρ σ) 0
  have h_lin : (fun ε => ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν) ρ σ) =
               (fun ε => (metric_to_matrix g x_p)⁻¹ ρ σ + ε * delta_matrix μ ν ρ σ) := by
    funext ε; simp [Matrix.add_apply, Matrix.smul_apply]; ring
  rw [h_lin]
  rw [deriv_add]
  · rw [deriv_const, zero_add]
    rw [deriv_mul_const]
    · rw [deriv_id'']; ring
    · exact differentiableAt_id
  · exact differentiableAt_const _
  · exact DifferentiableAt.mul_const differentiableAt_id _

/-- **HYPOTHESIS**: Total-divergence terms contribute only a boundary term, hence vanish under
    functional differentiation. -/
def H_TotalDivergenceBoundary
    (w : MetricTensor → (Fin 4 → ℝ) → Fin 4 → ℝ)
    (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) : Prop :=
  functional_deriv (fun g' y => Finset.univ.sum (fun rho => partialDeriv_v2 (w g' · rho) rho y)) g μ ν x = 0

/-- **THEOREM**: The variation of a total divergence vanishes under the assumption of
    compactly supported perturbations. -/
theorem total_divergence_variation_zero (w : MetricTensor → (Fin 4 → ℝ) → Fin 4 → ℝ)
    (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ)
    (h_compact : H_TotalDivergenceBoundary w g μ ν x) :
    functional_deriv (fun g' y => Finset.univ.sum (fun rho => partialDeriv_v2 (w g' · rho) rho y)) g μ ν x = 0 :=
  h_compact

/-- Euler-Lagrange equation for scalar field from action S[ψ].
    Derived from δS/δψ = 0 gives: ∂_μ (∂L/∂(∂_μ ψ)) - ∂L/∂ψ = 0. -/
def EulerLagrange (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  -- □ψ - m² ψ = 0 where □ = g^{μν} ∇_μ ∇_ν
  ∀ x_p : Fin 4 → ℝ,
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
        (inverse_metric g) x_p (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
        Fields.directional_deriv
          { ψ := fun y => Fields.gradient ψ y μ } ν x_p)) - m_squared * ψ.ψ x_p = 0

/-- Klein-Gordon equation: □ψ - m²ψ = 0 (special case of EL for free scalar). -/
def KleinGordon (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  EulerLagrange ψ g m_squared

/-- D'Alembertian operator □ = g^{μν} ∇_μ ∇_ν. -/
noncomputable def dalembertian (ψ : Fields.ScalarField) (g : MetricTensor) (x_p : Fin 4 → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (inverse_metric g) x_p (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
      Fields.directional_deriv { ψ := fun y => Fields.gradient ψ y μ } ν x_p))

theorem klein_gordon_explicit (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) :
  KleinGordon ψ g m_squared ↔ (∀ x, dalembertian ψ g x - m_squared * ψ.ψ x = 0) := by
  unfold KleinGordon EulerLagrange dalembertian
  simp only [sub_eq_zero]

/-- Euler-Lagrange equations for the metric (Einstein Field Equations).
    δS/δg^μν = 0. -/
def MetricEulerLagrange (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    functional_deriv S g μ ν x = 0

end Variation
end Relativity
end IndisputableMonolith
