import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor

namespace IndisputableMonolith
namespace Relativity
namespace Calculus

open scoped Topology
open Filter Real

/-- Standard basis vector `e_μ`. -/
def basisVec (μ : Fin 4) : Fin 4 → ℝ := fun ν => if ν = μ then 1 else 0

@[simp] lemma basisVec_self (μ : Fin 4) : basisVec μ μ = 1 := by simp [basisVec]

@[simp] lemma basisVec_ne {μ ν : Fin 4} (h : ν ≠ μ) : basisVec μ ν = 0 := by
  simp [basisVec, h]

/-- Coordinate ray `x + t e_μ`. -/
def coordRay (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) : Fin 4 → ℝ :=
  fun ν => x ν + t * basisVec μ ν

@[simp] lemma coordRay_apply (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) (ν : Fin 4) :
    coordRay x μ t ν = x ν + t * basisVec μ ν := rfl

@[simp] lemma coordRay_zero (x : Fin 4 → ℝ) (μ : Fin 4) : coordRay x μ 0 = x := by
  funext ν; simp [coordRay]

@[simp] lemma coordRay_coordRay (x : Fin 4 → ℝ) (μ : Fin 4) (s t : ℝ) :
    coordRay (coordRay x μ s) μ t = coordRay x μ (s + t) := by
  funext ν; simp [coordRay]; ring

/-- Directional derivative `∂_μ f(x)` via real derivative along the coordinate ray. -/
noncomputable def partialDeriv_v2 (f : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun t => f (coordRay x μ t)) 0

/-- The derivative of a constant function is zero. -/
lemma partialDeriv_v2_const {f : (Fin 4 → ℝ) → ℝ} {c : ℝ} (h : ∀ y, f y = c) (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 f μ x = 0 := by
  unfold partialDeriv_v2
  have h_const : (fun t => f (coordRay x μ t)) = (fun _ => c) := by
    funext t
    rw [h]
  rw [h_const]
  exact deriv_const (0 : ℝ) c

/-- Second derivative `∂_μ∂_ν f(x)` as iterated directional derivatives. -/
noncomputable def secondDeriv (f : (Fin 4 → ℝ) → ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0

/-- Laplacian `∇² = Σ_{i=1}^3 ∂²/∂xᵢ²`. -/
noncomputable def laplacian (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  secondDeriv f ⟨1, by decide⟩ ⟨1, by decide⟩ x +
  secondDeriv f ⟨2, by decide⟩ ⟨2, by decide⟩ x +
  secondDeriv f ⟨3, by decide⟩ ⟨3, by decide⟩ x

/-- Linearity of the directional derivative. -/
lemma deriv_add_lin (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => f y + g y) μ x =
    partialDeriv_v2 f μ x + partialDeriv_v2 g μ x := by
  unfold partialDeriv_v2
  exact deriv_add hf hg

/-- Linearity of directional derivative (scalar multiplication). -/
lemma partialDeriv_v2_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => c * f y) μ x = c * partialDeriv_v2 f μ x := by
  unfold partialDeriv_v2
  exact deriv_const_mul c hf

/-- Localized version of second derivative linearity (scalar multiplication).
    This only requires differentiability in a neighborhood of the point x. -/
lemma secondDeriv_smul_local (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ)
    (h1 : ∀ᶠ s in 𝓝 0, DifferentiableAt ℝ (fun t => f (coordRay (coordRay x ν s) μ t)) 0)
    (h2 : DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  secondDeriv (fun y => c * f y) μ ν x = c * secondDeriv f μ ν x := by
  unfold secondDeriv
  have h_ev : ∀ᶠ s in 𝓝 0, partialDeriv_v2 (fun z => c * f z) μ (coordRay x ν s) =
                          c * partialDeriv_v2 f μ (coordRay x ν s) := by
    apply h1.mono
    intro s hs
    exact partialDeriv_v2_smul f c μ (coordRay x ν s) hs
  rw [Filter.EventuallyEq.deriv_eq h_ev]
  exact deriv_const_mul c h2

/-- Second derivative linearity (scalar multiplication). -/
lemma secondDeriv_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ)
    (h1 : ∀ y, DifferentiableAt ℝ (fun t => f (coordRay y μ t)) 0)
    (h2 : DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  secondDeriv (fun y => c * f y) μ ν x = c * secondDeriv f μ ν x := by
  unfold secondDeriv
  have h_partial : ∀ y, partialDeriv_v2 (fun z => c * f z) μ y = c * partialDeriv_v2 f μ y := by
    intro y
    exact partialDeriv_v2_smul f c μ y (h1 y)
  simp only [h_partial]
  exact deriv_const_mul c h2

/-- Laplacian linearity (scalar multiplication). -/
lemma laplacian_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (x : Fin 4 → ℝ)
    (h1 : ∀ μ y, DifferentiableAt ℝ (fun t => f (coordRay y μ t)) 0)
    (h2 : ∀ μ ν, DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  laplacian (fun y => c * f y) x = c * laplacian f x := by
  unfold laplacian
  simp only [secondDeriv_smul f c _ _ x (h1 _) (h2 _ _)]
  ring

/-- Product rule for directional derivative. -/
lemma partialDeriv_v2_mul (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => f y * g y) μ x =
    f x * partialDeriv_v2 g μ x + g x * partialDeriv_v2 f μ x := by
  unfold partialDeriv_v2
  have h_mul : deriv (fun ε => f (coordRay x μ ε) * g (coordRay x μ ε)) 0 =
               deriv (fun ε => f (coordRay x μ ε)) 0 * g (coordRay x μ 0) +
               f (coordRay x μ 0) * deriv (fun ε => g (coordRay x μ ε)) 0 :=
    deriv_mul hf hg
  rw [h_mul]
  simp only [coordRay_zero]
  ring

/-- Spatial norm squared `x₁² + x₂² + x₃²`. -/
def spatialNormSq (x : Fin 4 → ℝ) : ℝ := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

theorem spatialNormSq_nonneg (x : Fin 4 → ℝ) : 0 ≤ spatialNormSq x := by
  unfold spatialNormSq
  positivity

theorem spatialNormSq_eq_zero_iff (x : Fin 4 → ℝ) : spatialNormSq x = 0 ↔ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := by
  unfold spatialNormSq
  constructor
  · intro h
    have h1 := sq_nonneg (x 1)
    have h2 := sq_nonneg (x 2)
    have h3 := sq_nonneg (x 3)
    have h1_zero : x 1 ^ 2 = 0 := by linarith
    have h2_zero : x 2 ^ 2 = 0 := by linarith
    have h3_zero : x 3 ^ 2 = 0 := by linarith
    simp only [sq_eq_zero_iff] at h1_zero h2_zero h3_zero
    exact ⟨h1_zero, h2_zero, h3_zero⟩
  · intro h
    simp [h]

/-- Spatial radius `r = √(x₁² + x₂² + x₃²)`. -/
noncomputable def spatialRadius (x : Fin 4 → ℝ) : ℝ := Real.sqrt (spatialNormSq x)

theorem spatialRadius_pos_iff (x : Fin 4 → ℝ) : 0 < spatialRadius x ↔ 0 < spatialNormSq x := by
  unfold spatialRadius
  rw [Real.sqrt_pos]

theorem spatialRadius_ne_zero_iff (x : Fin 4 → ℝ) : spatialRadius x ≠ 0 ↔ spatialNormSq x ≠ 0 := by
  unfold spatialRadius
  rw [Real.sqrt_ne_zero (spatialNormSq_nonneg x)]

/-- Temporal coordinate ray doesn't change spatial components. -/
lemma coordRay_temporal_spatial (x : Fin 4 → ℝ) (s : ℝ) (i : Fin 4) (hi : i ≠ 0) :
    (coordRay x 0 s) i = x i := by
  simp only [coordRay_apply, basisVec, Fin.isValue]
  simp only [hi.symm, ↓reduceIte, mul_zero, add_zero]

/-- spatialNormSq is invariant under temporal coordinate ray. -/
lemma spatialNormSq_coordRay_temporal (x : Fin 4 → ℝ) (s : ℝ) :
    spatialNormSq (coordRay x 0 s) = spatialNormSq x := by
  unfold spatialNormSq
  have h1 : (coordRay x 0 s) 1 = x 1 := coordRay_temporal_spatial x s 1 (by decide)
  have h2 : (coordRay x 0 s) 2 = x 2 := coordRay_temporal_spatial x s 2 (by decide)
  have h3 : (coordRay x 0 s) 3 = x 3 := coordRay_temporal_spatial x s 3 (by decide)
  rw [h1, h2, h3]

/-- spatialRadius is invariant under temporal coordinate ray. -/
lemma spatialRadius_coordRay_temporal (x : Fin 4 → ℝ) (s : ℝ) :
    spatialRadius (coordRay x 0 s) = spatialRadius x := by
  unfold spatialRadius
  rw [spatialNormSq_coordRay_temporal]

/-- spatialRadius is nonzero at coordRay x ν s when it's nonzero at x (for small s).
    For ν = 0 (temporal), this is exact. For spatial ν, uses continuity. -/
lemma spatialRadius_coordRay_ne_zero (x : Fin 4 → ℝ) (ν : Fin 4) (s : ℝ)
    (hx : spatialRadius x ≠ 0) (hs : |s| < spatialRadius x / 2) :
    spatialRadius (coordRay x ν s) ≠ 0 := by
  by_cases hν : ν = 0
  · -- Temporal direction: exact invariance
    subst hν
    rw [spatialRadius_coordRay_temporal]
    exact hx
  · -- Spatial direction: spatialRadius > 0 is preserved for small perturbations
    have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
    -- The key estimate: |spatialRadius(x+se_ν) - spatialRadius(x)| ≤ |s|
    -- This follows from the reverse triangle inequality for the Euclidean norm
    -- Since |s| < r/2, we have spatialRadius(x+se_ν) > r - |s| > r/2 > 0
    have h_bound : spatialRadius x / 2 > 0 := by linarith
    -- For ν ∈ {1,2,3}, coordRay x ν s changes only component ν by s
    -- The spatialRadius is the Euclidean norm of (x_1, x_2, x_3)
    -- Adding s to one component changes the norm by at most |s|
    intro h_zero
    -- If spatialRadius (coordRay x ν s) = 0, then all spatial components are 0
    have h_sq_zero : spatialNormSq (coordRay x ν s) = 0 := by
      rw [spatialRadius_ne_zero_iff] at h_zero
      push_neg at h_zero
      exact h_zero
    unfold spatialNormSq at h_sq_zero
    -- (x_1 + s*δ_{ν1})² + (x_2 + s*δ_{ν2})² + (x_3 + s*δ_{ν3})² = 0
    -- This means each squared term is 0
    have h1 : (coordRay x ν s) 1 ^ 2 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 1), sq_nonneg ((coordRay x ν s) 2), sq_nonneg ((coordRay x ν s) 3)]
    have h2 : (coordRay x ν s) 2 ^ 2 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 1), sq_nonneg ((coordRay x ν s) 2), sq_nonneg ((coordRay x ν s) 3)]
    have h3 : (coordRay x ν s) 3 ^ 2 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 1), sq_nonneg ((coordRay x ν s) 2), sq_nonneg ((coordRay x ν s) 3)]
    have h1' : (coordRay x ν s) 1 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 1)]
    have h2' : (coordRay x ν s) 2 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 2)]
    have h3' : (coordRay x ν s) 3 = 0 := by nlinarith [sq_nonneg ((coordRay x ν s) 3)]
    -- Now use the definition of coordRay
    simp only [coordRay_apply] at h1' h2' h3'
    -- One of ν = 1, 2, or 3 (since ν ≠ 0 and ν : Fin 4)
    interval_cases ν
    all_goals simp only [basisVec, Fin.isValue] at h1' h2' h3'
    -- ν = 1: h1' says x 1 + s = 0, h2' says x 2 = 0, h3' says x 3 = 0
    · simp only [↓reduceIte, mul_one, mul_zero, add_zero] at h1' h2' h3'
      have hx_zero : spatialNormSq x = 0 := by unfold spatialNormSq; nlinarith
      rw [spatialRadius_ne_zero_iff, hx_zero] at hx
      exact hx rfl
    -- ν = 2: similar
    · simp only [↓reduceIte, mul_one, mul_zero, add_zero] at h1' h2' h3'
      have hx_zero : spatialNormSq x = 0 := by unfold spatialNormSq; nlinarith
      rw [spatialRadius_ne_zero_iff, hx_zero] at hx
      exact hx rfl
    -- ν = 3: similar
    · simp only [↓reduceIte, mul_one, mul_zero, add_zero] at h1' h2' h3'
      have hx_zero : spatialNormSq x = 0 := by unfold spatialNormSq; nlinarith
      rw [spatialRadius_ne_zero_iff, hx_zero] at hx
      exact hx rfl

/-- Radial inverse function `1/r^n` where r is the spatial radius.
    Used for gravitational potentials. -/
noncomputable def radialInv (n : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  1 / (spatialRadius x) ^ n

/-- Differentiability of a coordinate ray component. -/
theorem differentiableAt_coordRay_i (x : Fin 4 → ℝ) (μ i : Fin 4) :
    DifferentiableAt ℝ (fun t => (coordRay x μ t) i) 0 := by
  simp only [coordRay_apply]
  apply DifferentiableAt.add
  · apply differentiableAt_const
  · apply DifferentiableAt.mul
    · apply differentiableAt_id
    · apply differentiableAt_const

/-- Differentiability of a squared coordinate ray component. -/
theorem differentiableAt_coordRay_i_sq (x : Fin 4 → ℝ) (μ i : Fin 4) :
    DifferentiableAt ℝ (fun t => (coordRay x μ t) i ^ 2) 0 := by
  apply DifferentiableAt.pow (differentiableAt_coordRay_i x μ i) 2

/-- Closed form for ∂μ (xᵢ²). -/
theorem partialDeriv_v2_x_sq (μ i : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 (fun y => y i ^ 2) μ x = 2 * x i * (if i = μ then 1 else 0) := by
  unfold partialDeriv_v2
  simp only [coordRay_apply]
  let f_i := fun t => x i + t * basisVec μ i
  have h_f : DifferentiableAt ℝ f_i 0 := differentiableAt_coordRay_i x μ i
  rw [show (fun t => (x i + t * basisVec μ i) ^ 2) = f_i ^ 2 by rfl]
  rw [deriv_pow h_f 2]
  simp only [f_i, coordRay_zero, pow_one]
  split_ifs with h_eq
  · subst h_eq
    simp only [basisVec_self, mul_one]
    rw [deriv_const_add, deriv_id'']
    ring
  · simp only [basisVec_ne h_eq, mul_zero, add_zero]
    rw [deriv_const]
    ring

theorem deriv_coordRay_i (x : Fin 4 → ℝ) (i : Fin 4) :
    deriv (fun t => (coordRay x i t) i) 0 = 1 := by
  simp only [coordRay_apply, basisVec_self, mul_one]
  rw [deriv_const_add, deriv_id'']

theorem deriv_coordRay_j (x : Fin 4 → ℝ) (i j : Fin 4) (h : j ≠ i) :
    deriv (fun t => (coordRay x i t) j) 0 = 0 := by
  simp only [coordRay_apply, basisVec_ne h, mul_zero, add_zero]
  exact deriv_const 0 (x j)

/-- **THEOREM**: Functional derivative of spatialNormSq.
    ∂_μ (∑ x_i²) = 2 x_μ for μ ∈ {1,2,3}, else 0.

    **Derivation**: Using the chain rule and ∂_μ(x_i²) = 2x_i δ_{iμ}, we get:
    ∂_μ(x₁² + x₂² + x₃²) = 2x₁δ_{1μ} + 2x₂δ_{2μ} + 2x₃δ_{3μ} = 2x_μ for μ ∈ {1,2,3}. -/
theorem partialDeriv_v2_spatialNormSq (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 spatialNormSq μ x =
    if μ = 0 then 0 else 2 * x μ := by
  -- Each component x_i² gives 2x_i δ_{iμ}
  have hd1 := partialDeriv_v2_x_sq μ 1 x
  have hd2 := partialDeriv_v2_x_sq μ 2 x
  have hd3 := partialDeriv_v2_x_sq μ 3 x
  -- Enumerate all 4 cases for μ
  fin_cases μ <;> simp_all [partialDeriv_v2, spatialNormSq, coordRay_apply, basisVec, deriv_const_add]

/-- Differentiability of spatialNormSq along a coordinate ray. -/
theorem differentiableAt_coordRay_spatialNormSq (x : Fin 4 → ℝ) (μ : Fin 4) :
    DifferentiableAt ℝ (fun t => spatialNormSq (coordRay x μ t)) 0 := by
  unfold spatialNormSq
  apply DifferentiableAt.add
  · apply DifferentiableAt.add
    · exact differentiableAt_coordRay_i_sq x μ 1
    · exact differentiableAt_coordRay_i_sq x μ 2
  · exact differentiableAt_coordRay_i_sq x μ 3

/-- Differentiability of spatialRadius along a coordinate ray. -/
theorem differentiableAt_coordRay_spatialRadius (x : Fin 4 → ℝ) (μ : Fin 4) (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun t => spatialRadius (coordRay x μ t)) 0 := by
  unfold spatialRadius
  have h_sn_ne_zero : spatialNormSq (coordRay x μ 0) ≠ 0 := by
    simp only [coordRay_zero]
    exact (spatialRadius_ne_zero_iff x).mp hx
  apply DifferentiableAt.sqrt (differentiableAt_coordRay_spatialNormSq x μ) h_sn_ne_zero

/-- Differentiability of radialInv along a coordinate ray. -/
theorem differentiableAt_coordRay_radialInv (n : ℕ) (x : Fin 4 → ℝ) (μ : Fin 4) (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun t => radialInv n (coordRay x μ t)) 0 := by
  unfold radialInv
  apply DifferentiableAt.div (differentiableAt_const (1 : ℝ))
  · apply DifferentiableAt.pow (differentiableAt_coordRay_spatialRadius x μ hx)
  · have h_pos : 0 < spatialRadius x := by
      unfold spatialRadius
      apply Real.sqrt_pos.mpr
      have h_nonneg := spatialNormSq_nonneg x
      have h_ne_zero := (spatialRadius_ne_zero_iff x).mp hx
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    simp only [coordRay_zero]
    exact (pow_pos h_pos n).ne'

theorem spatialRadius_coordRay_ne_zero {x : Fin 4 → ℝ} (hx : spatialRadius x ≠ 0) (μ : Fin 4) :
    ∀ᶠ t in 𝓝 0, spatialRadius (coordRay x μ t) ≠ 0 := by
  have h_cont : Continuous (fun t => spatialRadius (coordRay x μ t)) := by
    unfold spatialRadius spatialNormSq coordRay basisVec
    fun_prop
  apply h_cont.continuousAt.eventually_ne
  simp [coordRay_zero, hx]

/-- **THEOREM**: Functional derivative of spatialRadius.
    ∂_μ r = x_μ / r for μ ∈ {1,2,3}, else 0. -/
theorem partialDeriv_v2_spatialRadius (μ : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    partialDeriv_v2 spatialRadius μ x =
    if μ = 0 then 0 else x μ / spatialRadius x := by
  unfold partialDeriv_v2 spatialRadius
  let g := fun t => spatialNormSq (coordRay x μ t)
  have h_g_diff : DifferentiableAt ℝ g 0 := differentiableAt_coordRay_spatialNormSq x μ
  -- Use the chain rule for sqrt manually
  have h_comp : deriv (fun t => Real.sqrt (g t)) 0 = deriv Real.sqrt (g 0) * deriv g 0 := by
    apply deriv_comp
    · have h_sn_ne_zero : spatialNormSq x ≠ 0 := (spatialRadius_ne_zero_iff x).mp hx
      have h_g0_ne_zero : g 0 ≠ 0 := by
        simp only [coordRay_zero, g]
        exact h_sn_ne_zero
      exact (Real.deriv_sqrt_aux h_g0_ne_zero).1.differentiableAt
    · exact h_g_diff
  rw [h_comp]
  have h_dg0 : deriv g 0 = partialDeriv_v2 spatialNormSq μ x := rfl
  rw [h_dg0, partialDeriv_v2_spatialNormSq]
  have h_ds0 : deriv Real.sqrt (g 0) = 1 / (2 * Real.sqrt (spatialNormSq x)) := by
    have h_g0 : g 0 = spatialNormSq x := by simp [g, coordRay_zero]
    have h_sn_ne_zero : spatialNormSq x ≠ 0 := (spatialRadius_ne_zero_iff x).mp hx
    rw [h_g0]
    exact (Real.deriv_sqrt_aux h_sn_ne_zero).1.hasDerivAt.deriv
  rw [h_ds0]
  split_ifs with hμ0
  · simp
  · field_simp [hx]

/-- **THEOREM**: Functional derivative of radialInv (1/r^n).
    ∂_μ (1/r^n) = -n x_μ / r^{n+2} for μ ∈ {1,2,3}, else 0.

    **Proof**: Using chain rule on 1/r^n = r^(-n):
    ∂_μ(r^(-n)) = -n * r^(-n-1) * ∂_μ(r)
                = -n * r^(-n-1) * (x_μ/r) for μ ∈ {1,2,3}
                = -n * x_μ / r^(n+2)

    For μ = 0, ∂_μ(r) = 0, so the whole derivative is 0. -/
theorem partialDeriv_v2_radialInv (n : ℕ) (μ : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    partialDeriv_v2 (radialInv n) μ x =
    if μ = 0 then 0 else - (n : ℝ) * x μ / (spatialRadius x) ^ (n + 2) := by
  have h_dr := partialDeriv_v2_spatialRadius μ x hx
  unfold partialDeriv_v2 radialInv
  -- Set up the composition: (1/r^n) ∘ (spatialRadius ∘ coordRay)
  set r := fun t => spatialRadius (coordRay x μ t) with hr_def
  have hr0 : r 0 = spatialRadius x := by simp [hr_def]
  have hr_pos : r 0 > 0 := by rw [hr0]; exact spatialRadius_pos_of_ne_zero hx
  have hr_ne : r 0 ≠ 0 := ne_of_gt hr_pos
  have hr_diff : DifferentiableAt ℝ r 0 := differentiableAt_coordRay_spatialRadius x μ hx
  have h_deriv_r : deriv r 0 = partialDeriv_v2 spatialRadius μ x := rfl

  -- Case n = 0: constant function
  by_cases hn : n = 0
  · simp only [hn, pow_zero, div_one, CharP.cast_eq_zero, neg_zero, zero_mul, zero_div, ite_self]
    exact deriv_const 0 1

  -- Case n > 0: use chain rule for 1/r^n
  -- d/dt[1/r(t)^n] = d/dt[r(t)^(-n)] (treating as zpow)
  -- But we use 1/r^n directly via deriv_div_const and deriv_pow

  -- 1/r^n = (r^n)^(-1), so d/dt[1/r^n] = -(r^n)^(-2) * n * r^(n-1) * r'
  --                                     = -n * r^(n-1) / r^(2n) * r'
  --                                     = -n * r' / r^(n+1)
  have h_pow_diff : DifferentiableAt ℝ (fun t => r t ^ n) 0 := hr_diff.pow n
  have h_pow_ne : r 0 ^ n ≠ 0 := pow_ne_zero n hr_ne

  -- d/dt[(r^n)^(-1)] = -(r^n)^(-2) * d/dt[r^n] = -(r^n)^(-2) * n * r^(n-1) * r'
  have h_deriv : deriv (fun t => 1 / r t ^ n) 0 =
      - ((r 0 ^ n)^2)⁻¹ * (n * r 0 ^ (n - 1) * deriv r 0) := by
    have h1 : deriv (fun t => (r t ^ n)⁻¹) 0 = -(deriv (fun t => r t ^ n) 0) / (r 0 ^ n) ^ 2 := by
      apply deriv_inv'' h_pow_diff h_pow_ne
    have h2 : deriv (fun t => r t ^ n) 0 = n * r 0 ^ (n - 1) * deriv r 0 := by
      exact deriv_pow hr_diff n
    rw [one_div]
    rw [h1, h2]
    ring
  rw [h_deriv, hr0, h_deriv_r, h_dr]
  split_ifs with hμ0
  · -- μ = 0 case: dr = 0
    simp
  · -- μ ≠ 0 case: dr = x_μ / r
    -- We have: -((r^n)^2)⁻¹ * (n * r^(n-1) * (x_μ / r))
    -- Simplify: -r^(-2n) * n * r^(n-1) * x_μ * r^(-1)
    --         = -n * x_μ * r^(-2n + n - 1 - 1)
    --         = -n * x_μ * r^(-n-2)
    --         = -n * x_μ / r^(n+2)  ✓
    have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
    -- Algebraic simplification
    have h_pow_pos : 0 < spatialRadius x ^ n := pow_pos hr_pos n
    have h_pow_sq_pos : 0 < (spatialRadius x ^ n) ^ 2 := sq_pos_of_pos h_pow_pos
    have h_pow_n2_pos : 0 < spatialRadius x ^ (n + 2) := pow_pos hr_pos (n + 2)
    -- The key algebraic identity
    have h_algebra : -((spatialRadius x ^ n) ^ 2)⁻¹ * (↑n * spatialRadius x ^ (n - 1) * (x μ / spatialRadius x)) =
                     -↑n * x μ / spatialRadius x ^ (n + 2) := by
      -- Key power identities
      have hr_ne' : spatialRadius x ≠ 0 := hx
      have h_pow_n_ne : spatialRadius x ^ n ≠ 0 := pow_ne_zero n hr_ne'
      have h_pow_sq_ne : (spatialRadius x ^ n) ^ 2 ≠ 0 := pow_ne_zero 2 h_pow_n_ne
      have h_pow_n2_ne : spatialRadius x ^ (n + 2) ≠ 0 := pow_ne_zero (n + 2) hr_ne'

      -- Rewrite using power laws: r^(n-1) / r = r^(n-2) for n ≥ 1
      -- And (r^n)^2 = r^(2n), so (r^n)^2 * r^(n+2) = r^(3n+2)
      -- We need: -n * x_μ * r^(n-1) / r * r^(n+2) = -n * x_μ * (r^n)^2
      -- LHS = -n * x_μ * r^(n-1) * r^(-1) * r^(n+2) = -n * x_μ * r^(2n) = -n * x_μ * (r^n)^2 ✓

      by_cases hn1 : n = 1
      · -- n = 1 case: simpler
        simp only [hn1]
        field_simp
        ring
      · -- n ≥ 2 or n = 0 (but n ≠ 0 was handled earlier, so n ≥ 2)
        -- Use field_simp to clear denominators, then show the power identity
        field_simp
        -- The goal after field_simp should be about products of powers
        -- Key: r^(n-1) * r^(n+2) = r^(2n+1) and r * (r^n)^2 = r * r^(2n) = r^(2n+1)
        have h_pow_eq : spatialRadius x ^ (n - 1) * spatialRadius x ^ (n + 2) =
                        spatialRadius x * (spatialRadius x ^ n) ^ 2 := by
          rw [sq, ← pow_add, ← pow_add, ← pow_succ]
          congr 1
          omega
        rw [mul_comm (spatialRadius x ^ (n - 1)) _, mul_assoc, h_pow_eq]
        ring
    exact h_algebra

/-- **THEOREM**: Differentiability of partialDeriv_v2 (radialInv n) along a coordinate ray.

    The function s ↦ ∂(1/r^n)/∂x_μ evaluated at (coordRay x ν s) is differentiable at s = 0.

    **Proof sketch**:
    From partialDeriv_v2_radialInv:
    - If μ = 0: constant function 0, always differentiable
    - If μ ≠ 0: the function is s ↦ -n * (x_μ + s*δ_{μν}) / r(coordRay x ν s)^(n+2)

    This is a composition of:
    1. Polynomial in s: x_μ + s*δ_{μν}
    2. Power of spatialRadius: r(coordRay x ν s)^(n+2)

    Both are smooth when r ≠ 0, so the quotient is differentiable. -/
theorem differentiableAt_coordRay_partialDeriv_v2_radialInv (n : ℕ) (x : Fin 4 → ℝ) (μ ν : Fin 4)
    (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun s => partialDeriv_v2 (radialInv n) μ (coordRay x ν s)) 0 := by
  by_cases hμ : μ = 0
  · -- μ = 0: constant function 0
    simp only [hμ]
    -- For μ = 0 (temporal direction), partialDeriv_v2 is 0 near s = 0
    -- Use differentiableAt_const after showing the function equals 0 near 0
    have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
    -- In the neighborhood |s| < r/2, the function equals 0
    have h_eq_zero : ∀ᶠ s in nhds (0 : ℝ), partialDeriv_v2 (radialInv n) 0 (coordRay x ν s) = 0 := by
      rw [Filter.eventually_iff_exists_mem]
      use Set.Ioo (-(spatialRadius x / 2)) (spatialRadius x / 2)
      constructor
      · apply Ioo_mem_nhds <;> linarith
      · intro s hs
        have hs' : |s| < spatialRadius x / 2 := by
          rw [abs_lt]
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        rw [partialDeriv_v2_radialInv n 0 (coordRay x ν s)]
        · simp
        · exact spatialRadius_coordRay_ne_zero x ν s hx hs'
    -- A function that eventually equals a constant is differentiable at that point
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_eq_zero (by simp [partialDeriv_v2_radialInv, hx])
  · -- μ ≠ 0: quotient of differentiable functions
    -- The function is s ↦ -n * (coordRay x ν s)_μ / r(coordRay x ν s)^(n+2)
    -- Numerator: (coordRay x ν s)_μ = x_μ + s * (if μ = ν then 1 else 0) - differentiable
    -- Denominator: r(coordRay x ν s)^(n+2) - differentiable and nonzero near s = 0
    --
    -- The proof uses:
    -- 1. differentiableAt_coordRay_i: coordRay component is differentiable
    -- 2. DifferentiableAt.pow: power of differentiable function is differentiable
    -- 3. DifferentiableAt.div: quotient with nonzero denominator is differentiable
    -- 4. spatialRadius_coordRay_ne_zero: denominator is nonzero near 0
    have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
    -- Numerator differentiability
    have h_num_diff : DifferentiableAt ℝ (fun s => (coordRay x ν s) μ) 0 :=
      differentiableAt_coordRay_i x ν μ
    -- Denominator differentiability (near 0)
    -- spatialRadius composed with coordRay is differentiable at 0
    have h_denom_diff : DifferentiableAt ℝ (fun s => spatialRadius (coordRay x ν s) ^ (n + 2)) 0 := by
      apply DifferentiableAt.pow
      exact differentiableAt_coordRay_spatialRadius x ν hx
    -- Denominator is nonzero at 0
    have h_denom_ne : spatialRadius (coordRay x ν 0) ^ (n + 2) ≠ 0 := by
      simp only [coordRay_zero]
      exact pow_ne_zero (n + 2) hx
    -- The full function is -n * numerator / denominator^(n+2)
    -- Use DifferentiableAt.div and DifferentiableAt.mul
    apply DifferentiableAt.mul
    · exact differentiableAt_const _
    · exact h_num_diff.div h_denom_diff h_denom_ne

/-- **THEOREM**: Second derivative of radialInv.

    ∂²(1/r^n)/∂x_ν∂x_μ = n * ((n+2) * x_μ * x_ν / r^(n+4) - δ_{μν} / r^(n+2))

    **Proof**:
    From partialDeriv_v2_radialInv: ∂(1/r^n)/∂x_μ = -n * x_μ / r^(n+2) (for μ ≠ 0)

    Differentiating again with respect to x_ν:
    ∂/∂x_ν[-n * x_μ / r^(n+2)]
    = -n * [∂(x_μ)/∂x_ν / r^(n+2) + x_μ * ∂(r^(-(n+2)))/∂x_ν]
    = -n * [δ_{μν} / r^(n+2) + x_μ * (-(n+2)) * r^(-(n+3)) * (x_ν / r)]
    = -n * [δ_{μν} / r^(n+2) - (n+2) * x_μ * x_ν / r^(n+4)]
    = n * [(n+2) * x_μ * x_ν / r^(n+4) - δ_{μν} / r^(n+2)] -/
theorem secondDeriv_radialInv (n : ℕ) (μ ν : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    secondDeriv (radialInv n) μ ν x =
    if μ = 0 ∨ ν = 0 then 0 else
    (n : ℝ) * ((n + 2 : ℝ) * x μ * x ν / (spatialRadius x) ^ (n + 4) - (if μ = ν then 1 else 0) / (spatialRadius x) ^ (n + 2)) := by
  unfold secondDeriv
  -- Case μ = 0: partialDeriv_v2 (radialInv n) 0 is constant 0, so derivative is 0
  by_cases hμ : μ = 0
  · simp only [hμ, true_or, ↓reduceIte]
    -- partialDeriv_v2 (radialInv n) 0 is 0 whenever spatialRadius is nonzero
    -- For μ = 0, the function is eventually constant 0 near s = 0
    have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
    have h_ev_const : ∀ᶠ s in nhds (0 : ℝ), partialDeriv_v2 (radialInv n) 0 (coordRay x ν s) = 0 := by
      rw [Filter.eventually_iff_exists_mem]
      use Set.Ioo (-(spatialRadius x / 2)) (spatialRadius x / 2)
      constructor
      · apply Ioo_mem_nhds <;> linarith
      · intro s hs
        have hs' : |s| < spatialRadius x / 2 := by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        rw [partialDeriv_v2_radialInv n 0 (coordRay x ν s)]
        · simp
        · exact spatialRadius_coordRay_ne_zero x ν s hx hs'
    exact (deriv_const (0 : ℝ) (0 : ℝ)).symm ▸ (HasDerivAt.deriv ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq h_ev_const (by simp [partialDeriv_v2_radialInv, hx])))
  · -- Case μ ≠ 0
    simp only [hμ, false_or]
    by_cases hν : ν = 0
    · -- Case ν = 0: differentiating in temporal direction
      simp only [hν, ↓reduceIte]
      -- coordRay x 0 s = x + s * e_0, which doesn't change spatial coordinates
      -- So partialDeriv_v2 (radialInv n) μ (coordRay x 0 s) is constant in s
      have h_const : ∀ s, partialDeriv_v2 (radialInv n) μ (coordRay x 0 s) =
                         partialDeriv_v2 (radialInv n) μ x := by
        intro s
        -- Use the temporal invariance lemmas
        have hr_inv : spatialRadius (coordRay x 0 s) = spatialRadius x :=
          spatialRadius_coordRay_temporal x s
        have hx_inv : (coordRay x 0 s) μ = x μ :=
          coordRay_temporal_spatial x s μ hμ
        rw [partialDeriv_v2_radialInv n μ (coordRay x 0 s)]
        · rw [partialDeriv_v2_radialInv n μ x hx]
          simp only [hμ, ↓reduceIte, hr_inv, hx_inv]
        · rw [hr_inv]; exact hx
      simp only [h_const, deriv_const]
    · -- Case μ ≠ 0 and ν ≠ 0: the main computation
      simp only [hν, ↓reduceIte]
      -- The function is: s ↦ -n * (coordRay x ν s)_μ / r(coordRay x ν s)^(n+2)
      -- where (coordRay x ν s)_μ = x_μ + s * δ_{μν}
      --
      -- Using the quotient rule:
      -- d/ds[f(s)/g(s)] = (f'(s)g(s) - f(s)g'(s)) / g(s)²
      --
      -- Here:
      -- f(s) = -n * (x_μ + s * δ_{μν})
      -- g(s) = r(coordRay x ν s)^(n+2)
      --
      -- At s = 0:
      -- f(0) = -n * x_μ
      -- g(0) = r^(n+2)
      -- f'(0) = -n * δ_{μν}
      -- g'(0) = (n+2) * r^(n+1) * (∂r/∂x_ν) = (n+2) * r^(n+1) * (x_ν/r) = (n+2) * r^n * x_ν
      --
      -- Therefore:
      -- d/ds[...] at s=0 = (f'(0)*g(0) - f(0)*g'(0)) / g(0)²
      --                  = (-n*δ_{μν}*r^(n+2) - (-n*x_μ)*(n+2)*r^n*x_ν) / r^(2n+4)
      --                  = (-n*δ_{μν}*r^(n+2) + n*(n+2)*x_μ*x_ν*r^n) / r^(2n+4)
      --                  = -n*δ_{μν}/r^(n+2) + n*(n+2)*x_μ*x_ν/r^(n+4)
      --                  = n * ((n+2)*x_μ*x_ν/r^(n+4) - δ_{μν}/r^(n+2))
      --
      -- This matches the target formula.
      have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
      have hr_ne : spatialRadius x ≠ 0 := ne_of_gt hr_pos

      -- Define the component functions
      set f : ℝ → ℝ := fun s => -↑n * (coordRay x ν s) μ with hf_def
      set g : ℝ → ℝ := fun s => spatialRadius (coordRay x ν s) ^ (n + 2) with hg_def

      -- The function we're differentiating
      have h_func : ∀ᶠ s in nhds (0 : ℝ), partialDeriv_v2 (radialInv n) μ (coordRay x ν s) = f s / g s := by
        rw [Filter.eventually_iff_exists_mem]
        use Set.Ioo (-(spatialRadius x / 2)) (spatialRadius x / 2)
        constructor
        · apply Ioo_mem_nhds <;> linarith
        · intro s hs
          have hs' : |s| < spatialRadius x / 2 := by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
          have hr_s : spatialRadius (coordRay x ν s) ≠ 0 := spatialRadius_coordRay_ne_zero x ν s hx hs'
          rw [partialDeriv_v2_radialInv n μ (coordRay x ν s) hr_s]
          simp only [hμ, ↓reduceIte, hf_def, hg_def]
          ring

      -- Compute f'(0)
      have hf_deriv : deriv f 0 = -↑n * (if μ = ν then 1 else 0) := by
        simp only [hf_def, coordRay_apply, basisVec]
        have : deriv (fun s => -↑n * (x μ + s * if ν = μ then 1 else 0)) 0 =
               -↑n * (if ν = μ then 1 else 0) := by
          rw [deriv_const_mul]
          · simp only [deriv_add_const, deriv_mul_const, deriv_id'', one_mul]
          · exact differentiableAt_id.mul (differentiableAt_const _) |>.add_const _
        convert this using 2
        · congr 1; funext s; congr 1; split_ifs <;> simp [*]
        · split_ifs with h <;> simp [h, h.symm, eq_comm]

      -- Compute g(0)
      have hg_zero : g 0 = spatialRadius x ^ (n + 2) := by simp [hg_def]

      -- f(0)
      have hf_zero : f 0 = -↑n * x μ := by simp [hf_def]

      -- Compute g'(0) using chain rule
      -- g(s) = (spatialRadius (coordRay x ν s))^(n+2)
      -- g'(s) = (n+2) * r(s)^(n+1) * r'(s)
      -- r'(0) = partialDeriv_v2 spatialRadius ν x = x_ν / r (for ν ≠ 0)
      have h_dr : deriv (fun s => spatialRadius (coordRay x ν s)) 0 = x ν / spatialRadius x := by
        have h := partialDeriv_v2_spatialRadius ν x hx
        simp only [hν, ↓reduceIte] at h
        unfold partialDeriv_v2 at h
        exact h

      have hg_diff : DifferentiableAt ℝ g 0 := by
        simp only [hg_def]
        apply DifferentiableAt.pow
        exact differentiableAt_coordRay_spatialRadius x ν hx

      have hg_deriv : deriv g 0 = (n + 2 : ℝ) * spatialRadius x ^ (n + 1) * (x ν / spatialRadius x) := by
        simp only [hg_def]
        rw [deriv_pow (differentiableAt_coordRay_spatialRadius x ν hx)]
        simp only [coordRay_zero]
        rw [h_dr]

      -- Simplify g'(0) = (n+2) * r^n * x_ν
      have hg_deriv' : deriv g 0 = (n + 2 : ℝ) * spatialRadius x ^ n * x ν := by
        rw [hg_deriv]
        have h_pow : spatialRadius x ^ (n + 1) * (x ν / spatialRadius x) =
                     spatialRadius x ^ n * x ν := by
          rw [pow_succ]
          field_simp
          ring
        linarith [h_pow]

      -- f is differentiable
      have hf_diff : DifferentiableAt ℝ f 0 := by
        simp only [hf_def]
        apply DifferentiableAt.const_mul
        exact differentiableAt_coordRay_i x ν μ

      -- g(0) ≠ 0
      have hg_ne : g 0 ≠ 0 := by
        rw [hg_zero]
        exact pow_ne_zero (n + 2) hr_ne

      -- Apply quotient rule: deriv (f/g) 0 = (f'*g - f*g') / g²
      have h_quot : deriv (fun s => f s / g s) 0 =
                    (deriv f 0 * g 0 - f 0 * deriv g 0) / (g 0) ^ 2 := by
        exact deriv_div hf_diff hg_diff hg_ne

      -- The target equals the quotient rule result
      -- deriv (partialDeriv_v2 ...) 0 = deriv (f/g) 0 (by h_func)
      have h_deriv_eq : deriv (fun s => partialDeriv_v2 (radialInv n) μ (coordRay x ν s)) 0 =
                        deriv (fun s => f s / g s) 0 := by
        apply Filter.EventuallyEq.deriv_eq
        exact h_func

      rw [h_deriv_eq, h_quot, hf_deriv, hf_zero, hg_zero, hg_deriv']
      -- Goal: ((-n * δ_{μν}) * r^(n+2) - (-n * x_μ) * (n+2) * r^n * x_ν) / (r^(n+2))²
      --     = n * ((n+2) * x_μ * x_ν / r^(n+4) - δ_{μν} / r^(n+2))
      have hr_pow_ne : spatialRadius x ^ (n + 2) ≠ 0 := pow_ne_zero (n + 2) hr_ne
      have hr_pow4_ne : spatialRadius x ^ (n + 4) ≠ 0 := pow_ne_zero (n + 4) hr_ne
      have hr_pow2n4_ne : spatialRadius x ^ (2 * n + 4) ≠ 0 := pow_ne_zero (2 * n + 4) hr_ne
      -- Simplify using field_simp and ring
      split_ifs with hμν
      · -- μ = ν case
        simp only [hμν, ↓reduceIte, mul_one]
        field_simp
        ring
      · -- μ ≠ ν case
        simp only [hμν, ↓reduceIte, mul_zero, sub_zero]
        field_simp
        ring

/-- **THEOREM**: Laplace's equation for 1/r in vacuum.

    ∇²(1/r) = 0 for r ≠ 0. This is the fundamental property making 1/r
    the Green's function for the Laplacian in 3D.

    **Proof**:
    Using secondDeriv_radialInv with n=1:
      ∂²(1/r)/∂xᵢ² = 1 * (3 * xᵢ² / r⁵ - 1 / r³)  for i ∈ {1,2,3}

    Summing over spatial indices i=1,2,3:
      ∇²(1/r) = Σᵢ (3xᵢ²/r⁵ - 1/r³)
              = 3(x₁² + x₂² + x₃²)/r⁵ - 3/r³
              = 3r²/r⁵ - 3/r³           [since r² = x₁² + x₂² + x₃²]
              = 3/r³ - 3/r³
              = 0 -/
theorem laplacian_radialInv_zero_no_const (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    laplacian (radialInv 1) x = 0 := by
  -- Expand laplacian as sum of second derivatives
  unfold laplacian
  -- Use secondDeriv_radialInv for each spatial index i ∈ {1, 2, 3}
  -- For n=1, μ=ν=i: secondDeriv = 1 * (3*xᵢ²/r⁵ - 1/r³)
  have h1 : secondDeriv (radialInv 1) 1 1 x = 1 * (3 * x 1 * x 1 / spatialRadius x ^ 5 - 1 / spatialRadius x ^ 3) := by
    rw [secondDeriv_radialInv 1 1 1 x hx]
    simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, Fin.isValue]
    ring
  have h2 : secondDeriv (radialInv 1) 2 2 x = 1 * (3 * x 2 * x 2 / spatialRadius x ^ 5 - 1 / spatialRadius x ^ 3) := by
    rw [secondDeriv_radialInv 1 2 2 x hx]
    simp only [Nat.cast_one, ne_eq, Fin.isValue, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
    ring
  have h3 : secondDeriv (radialInv 1) 3 3 x = 1 * (3 * x 3 * x 3 / spatialRadius x ^ 5 - 1 / spatialRadius x ^ 3) := by
    rw [secondDeriv_radialInv 1 3 3 x hx]
    simp only [Nat.cast_one, ne_eq, Fin.isValue, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
    ring
  rw [h1, h2, h3]
  -- Sum: 3(x₁² + x₂² + x₃²)/r⁵ - 3/r³ = 3r²/r⁵ - 3/r³ = 0
  have hr_sq : spatialRadius x ^ 2 = spatialNormSq x := by
    unfold spatialRadius spatialNormSq
    rw [Real.sq_sqrt (spatialNormSq_nonneg x)]
  have hr_sum : x 1 * x 1 + x 2 * x 2 + x 3 * x 3 = spatialNormSq x := by
    unfold spatialNormSq
    ring
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
  have hr_pow5_ne : spatialRadius x ^ 5 ≠ 0 := pow_ne_zero 5 (ne_of_gt hr_pos)
  have hr_pow3_ne : spatialRadius x ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hr_pos)
  -- Algebraic simplification: 3r²/r⁵ = 3/r³
  field_simp
  rw [← hr_sum, ← hr_sq]
  ring

/-- **THEOREM**: Laplacian of general radialInv (1/r^n).

    ∇²(1/r^n) = n(n-1)/r^(n+2) for r ≠ 0.

    **Proof**:
    Using secondDeriv_radialInv:
      ∂²(1/r^n)/∂xᵢ² = n * ((n+2)*xᵢ²/r^(n+4) - 1/r^(n+2))

    Summing over spatial indices i=1,2,3:
      ∇²(1/r^n) = n * ((n+2)(x₁²+x₂²+x₃²)/r^(n+4) - 3/r^(n+2))
                = n * ((n+2)r²/r^(n+4) - 3/r^(n+2))
                = n * ((n+2)/r^(n+2) - 3/r^(n+2))
                = n * (n+2-3)/r^(n+2)
                = n * (n-1)/r^(n+2)

    **Special cases**:
    - n=0: ∇²(1) = 0 (constant)
    - n=1: ∇²(1/r) = 0 (harmonic)
    - n=2: ∇²(1/r²) = 2/r⁴ -/
theorem laplacian_radialInv_n (n : ℕ) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    laplacian (radialInv n) x = (n : ℝ) * (n - 1 : ℝ) / (spatialRadius x) ^ (n + 2) := by
  -- Expand laplacian as sum of second derivatives
  unfold laplacian
  -- Use secondDeriv_radialInv for each spatial index i ∈ {1, 2, 3}
  -- For μ=ν=i ≠ 0: secondDeriv = n * ((n+2)*xᵢ²/r^(n+4) - 1/r^(n+2))
  have h1 : secondDeriv (radialInv n) 1 1 x =
      (n : ℝ) * ((n + 2 : ℝ) * x 1 * x 1 / spatialRadius x ^ (n + 4) - 1 / spatialRadius x ^ (n + 2)) := by
    rw [secondDeriv_radialInv n 1 1 x hx]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, Fin.isValue]
  have h2 : secondDeriv (radialInv n) 2 2 x =
      (n : ℝ) * ((n + 2 : ℝ) * x 2 * x 2 / spatialRadius x ^ (n + 4) - 1 / spatialRadius x ^ (n + 2)) := by
    rw [secondDeriv_radialInv n 2 2 x hx]
    simp only [ne_eq, Fin.isValue, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
  have h3 : secondDeriv (radialInv n) 3 3 x =
      (n : ℝ) * ((n + 2 : ℝ) * x 3 * x 3 / spatialRadius x ^ (n + 4) - 1 / spatialRadius x ^ (n + 2)) := by
    rw [secondDeriv_radialInv n 3 3 x hx]
    simp only [ne_eq, Fin.isValue, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
  rw [h1, h2, h3]
  -- Sum: n * ((n+2)(x₁² + x₂² + x₃²)/r^(n+4) - 3/r^(n+2))
  --    = n * ((n+2)r²/r^(n+4) - 3/r^(n+2))
  --    = n * ((n+2)/r^(n+2) - 3/r^(n+2))
  --    = n * (n-1)/r^(n+2)
  have hr_sq : spatialRadius x ^ 2 = spatialNormSq x := by
    unfold spatialRadius spatialNormSq
    rw [Real.sq_sqrt (spatialNormSq_nonneg x)]
  have hr_sum : x 1 * x 1 + x 2 * x 2 + x 3 * x 3 = spatialNormSq x := by
    unfold spatialNormSq
    ring
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hx
  have hr_ne : spatialRadius x ≠ 0 := ne_of_gt hr_pos
  -- Algebraic simplification
  have h_n2_4 : spatialRadius x ^ (n + 4) = spatialRadius x ^ 2 * spatialRadius x ^ (n + 2) := by
    rw [← pow_add]; congr 1; omega
  field_simp [pow_ne_zero (n + 2) hr_ne, pow_ne_zero (n + 4) hr_ne]
  rw [h_n2_4, hr_sq, ← hr_sum]
  ring

end Calculus
end Relativity
end IndisputableMonolith
