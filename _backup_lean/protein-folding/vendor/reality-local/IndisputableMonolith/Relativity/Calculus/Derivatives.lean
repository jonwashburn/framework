import Mathlib
import IndisputableMonolith.Relativity.Geometry

/-!
# Derivatives for Spacetime Functions

Implements directional derivatives using Mathlib.  We work with coordinate
rays in `ℝ⁴` (parametrised by `Fin 4`) and provide helper lemmas for radial
functions needed elsewhere in the code base.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Calculus

open scoped Topology
open Geometry

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
  funext ν; simp [coordRay, add_comm, add_left_comm, add_assoc, mul_add]

/-- Directional derivative `∂_μ f(x)` via real derivative along the coordinate ray. -/
noncomputable def partialDeriv_v2 (f : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun t => f (coordRay x μ t)) 0

/-- Second derivative `∂_μ∂_ν f(x)` as iterated directional derivatives. -/
noncomputable def secondDeriv (f : (Fin 4 → ℝ) → ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0

/-- Laplacian `∇² = Σ_{i=1}^3 ∂²/∂xᵢ²`. -/
noncomputable def laplacian (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  secondDeriv f 1 1 x + secondDeriv f 2 2 x + secondDeriv f 3 3 x

/-- Linearity of the directional derivative. -/
lemma deriv_add (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
  partialDeriv_v2 (fun y => f y + g y) μ x =
    partialDeriv_v2 f μ x + partialDeriv_v2 g μ x := by
  classical
  simp [partialDeriv_v2, deriv_add]

/-- Homogeneity of the directional derivative. -/
lemma deriv_smul (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
  partialDeriv_v2 (fun y => c * f y) μ x = c * partialDeriv_v2 f μ x := by
  classical
  simp [partialDeriv_v2, deriv_const_mul]

/-- Directional derivative of a constant. -/
lemma deriv_const (c : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 (fun _ => c) μ x = 0 := by
  classical
  simp [partialDeriv_v2]

/-- Product rule for directional derivatives. -/
lemma deriv_mul (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) :
  partialDeriv_v2 (fun y => f y * g y) μ x =
      partialDeriv_v2 f μ x * g x + f x * partialDeriv_v2 g μ x := by
  classical
  simp [partialDeriv_v2, deriv_mul]

/-- Laplacian is additive. -/
lemma laplacian_add (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    laplacian (fun y => f y + g y) x = laplacian f x + laplacian g x := by
  classical
  simp [laplacian, secondDeriv, deriv_add]

/-- Laplacian is homogeneous. -/
lemma laplacian_smul (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    laplacian (fun y => c * f y) x = c * laplacian f x := by
  classical
  simp [laplacian, secondDeriv, deriv_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Spatial norm squared `x₁² + x₂² + x₃²`. -/
@[simp] def spatialNormSq (x : Fin 4 → ℝ) : ℝ := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

/-- Spatial radius `r = √(x₁² + x₂² + x₃²)`. -/
@[simp] def spatialRadius (x : Fin 4 → ℝ) : ℝ := Real.sqrt (spatialNormSq x)

lemma spatialRadius_pos_of_ne_zero {x : Fin 4 → ℝ} (hr : spatialRadius x ≠ 0) :
    0 < spatialRadius x := by
  have hsq_ne : spatialNormSq x ≠ 0 := by
    intro h0
    have : spatialRadius x = 0 := by simpa [spatialRadius, h0] using Real.sqrt_eq_zero.mpr h0
    exact hr this
  have hsq_pos : 0 < spatialNormSq x :=
    lt_of_le_of_ne
      (by
        have hx1 := sq_nonneg (x 1)
        have hx2 := sq_nonneg (x 2)
        have hx3 := sq_nonneg (x 3)
        exact add_nonneg hx1 (add_nonneg hx2 hx3))
      (by simpa using hsq_ne.symm)
  simpa [spatialRadius] using Real.sqrt_pos.mpr hsq_pos

/-- Derivative of spatial radius along a spatial coordinate. -/
lemma hasDerivAt_spatialRadius_coordRay
    (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0) :
    HasDerivAt (fun t => spatialRadius (coordRay x μ t)) ((x μ) / spatialRadius x) 0 := by
  classical
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero hr
  fin_cases μ with
  | zero => cases hμ rfl
  | succ μ₀ =>
      cases μ₀ with
      | zero =>
          -- μ = 1
          let S := x ⟨2, by decide⟩ ^ 2 + x ⟨3, by decide⟩ ^ 2
          let g : ℝ → ℝ := fun t => (x ⟨1, by decide⟩ + t) ^ 2 + S
          have hder_g : HasDerivAt g (2 * x ⟨1, by decide⟩) 0 := by
            have h_linear : HasDerivAt (fun t : ℝ => x ⟨1, by decide⟩ + t) 1 0 :=
              (hasDerivAt_id 0).const_add _
            have h_sq := h_linear.pow 2
            have h_const : HasDerivAt (fun _ : ℝ => S) 0 0 := hasDerivAt_const _ _
            simpa [g] using h_sq.add h_const
          have hpos_g0 : 0 < g 0 := by
            have hx : g 0 = spatialNormSq x := by simp [g, spatialNormSq]
            have hxpos : 0 < spatialNormSq x :=
              by simpa [spatialRadius, hx] using Real.mul_self_pos.mpr hr_pos
            simpa [g, hx]
          have hsqrt := (Real.hasDerivAt_sqrt hpos_g0).comp 0 hder_g
          have :
              (fun t => spatialRadius (coordRay x ⟨1, by decide⟩ t))
                = fun t => Real.sqrt (g t) := by
            funext t; simp [spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
          simpa [this, spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
            using hsqrt
      | succ μ₁ =>
          cases μ₁ with
          | zero =>
              -- μ = 2
              let S := x ⟨1, by decide⟩ ^ 2 + x ⟨3, by decide⟩ ^ 2
              let g : ℝ → ℝ := fun t => (x ⟨2, by decide⟩ + t) ^ 2 + S
              have hder_g : HasDerivAt g (2 * x ⟨2, by decide⟩) 0 := by
                have h_linear : HasDerivAt (fun t : ℝ => x ⟨2, by decide⟩ + t) 1 0 :=
                  (hasDerivAt_id 0).const_add _
                have h_sq := h_linear.pow 2
                have h_const : HasDerivAt (fun _ : ℝ => S) 0 0 := hasDerivAt_const _ _
                simpa [g] using h_sq.add h_const
              have hpos_g0 : 0 < g 0 := by
                have hx : g 0 = spatialNormSq x := by simp [g, spatialNormSq]
                have hxpos : 0 < spatialNormSq x :=
                  by simpa [spatialRadius, hx] using Real.mul_self_pos.mpr hr_pos
                simpa [g, hx]
              have hsqrt := (Real.hasDerivAt_sqrt hpos_g0).comp 0 hder_g
              have :
                  (fun t => spatialRadius (coordRay x ⟨2, by decide⟩ t))
                    = fun t => Real.sqrt (g t) := by
                funext t; simp [spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
              simpa [this, spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
                using hsqrt
          | succ μ₂ =>
              cases μ₂ with
              | zero =>
                  -- μ = 3
                  let S := x ⟨1, by decide⟩ ^ 2 + x ⟨2, by decide⟩ ^ 2
                  let g : ℝ → ℝ := fun t => (x ⟨3, by decide⟩ + t) ^ 2 + S
                  have hder_g : HasDerivAt g (2 * x ⟨3, by decide⟩) 0 := by
                    have h_linear : HasDerivAt (fun t : ℝ => x ⟨3, by decide⟩ + t) 1 0 :=
                      (hasDerivAt_id 0).const_add _
                    have h_sq := h_linear.pow 2
                    have h_const : HasDerivAt (fun _ : ℝ => S) 0 0 := hasDerivAt_const _ _
                    simpa [g] using h_sq.add h_const
                  have hpos_g0 : 0 < g 0 := by
                    have hx : g 0 = spatialNormSq x := by simp [g, spatialNormSq]
                    have hxpos : 0 < spatialNormSq x :=
                      by simpa [spatialRadius, hx] using Real.mul_self_pos.mpr hr_pos
                    simpa [g, hx]
                  have hsqrt := (Real.hasDerivAt_sqrt hpos_g0).comp 0 hder_g
                  have :
                      (fun t => spatialRadius (coordRay x ⟨3, by decide⟩ t))
                        = fun t => Real.sqrt (g t) := by
                    funext t; simp [spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
                  simpa [this, spatialRadius, spatialNormSq, coordRay, basisVec, g, S]
                    using hsqrt
              | succ _ => cases hμ (by decide)

/-- Partial derivative of the spatial radius. -/
lemma partialDeriv_spatial_radius
    (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0) :
    partialDeriv_v2 spatialRadius μ x = (x μ) / spatialRadius x := by
  classical
  simpa [partialDeriv_v2] using
    (hasDerivAt_spatialRadius_coordRay x μ hμ hr).deriv

/-- The spatial radius is independent of time. -/
lemma partialDeriv_radius_time (x : Fin 4 → ℝ) :
    partialDeriv_v2 spatialRadius 0 x = 0 := by
  classical
  simp [partialDeriv_v2, coordRay, basisVec, spatialRadius, spatialNormSq]

/-- Radial derivative lemma: ∂μ F(r) = F'(r) · xμ / r. -/
lemma partialDeriv_radial
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) (μ : Fin 4)
    (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0)
    (hF : DifferentiableAt ℝ F (spatialRadius x)) :
    partialDeriv_v2 (fun y => F (spatialRadius y)) μ x =
      deriv F (spatialRadius x) * (x μ) / spatialRadius x := by
  classical
  have h_outer := hF.hasDerivAt
  have h_inner := hasDerivAt_spatialRadius_coordRay x μ hμ hr
  have h_comp := h_outer.comp 0 h_inner
  simpa [partialDeriv_v2] using h_comp.deriv

/-- The spatial radius stays non-zero near a point with positive radius. -/
lemma eventually_spatialRadius_ne_zero
    (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0) :
    (𝓝 (0 : ℝ)).Eventually (fun s => spatialRadius (coordRay x μ s) ≠ 0) := by
  classical
  set r := spatialRadius x with hr_def
  have hr0 : r ≠ 0 := by simpa [hr_def] using hr
  have h_tendsto :
      Tendsto (fun s : ℝ => spatialRadius (coordRay x μ s)) (𝓝 0) (𝓝 r) :=
    (hasDerivAt_spatialRadius_coordRay x μ hμ hr).continuousAt.tendsto
  have hopen : IsOpen {y : ℝ | y ≠ 0} := isClosed_singleton (0 : ℝ)).isOpen_compl
  have h_mem : {y : ℝ | y ≠ 0} ∈ nhds r := by
    refine hopen.mem_nhds ?_
    simpa [hr_def] using hr
  exact h_tendsto.eventually h_mem

/-- Helper: derivative of the inverse radius factor. -/
lemma hasDerivAt_inv_spatialRadius
    (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0) :
    HasDerivAt (fun s => (spatialRadius (coordRay x μ s))⁻¹)
      (-(x μ) / spatialRadius x ^ 3) 0 := by
  classical
  have h_ne : spatialRadius (coordRay x μ 0) ≠ 0 := by simpa [coordRay_zero] using hr
  have h_base := hasDerivAt_spatialRadius_coordRay x μ hμ hr
  have := (HasDerivAt.inv h_base h_ne)
  simpa [coordRay_zero, spatialRadius, pow_three, pow_two] using this

/-- Second derivative of a radial function along a spatial direction. -/
lemma secondDeriv_radial
    (F : ℝ → ℝ) (x : Fin 4 → ℝ) (μ : Fin 4)
    (hμ : μ ≠ 0) (hr : spatialRadius x ≠ 0)
    (hF : Differentiable ℝ F)
    (hF' : Differentiable ℝ fun r => deriv F r) :
    secondDeriv (fun y => F (spatialRadius y)) μ μ x =
      deriv (deriv F) (spatialRadius x) * (x μ / spatialRadius x) ^ 2
        + deriv F (spatialRadius x) *
            (1 / spatialRadius x - (x μ / spatialRadius x) ^ 2 / spatialRadius x) := by
  classical
  set r := spatialRadius x with hr_def
  have hr0 : r ≠ 0 := by simpa [hr_def] using hr
  set rfun := fun s : ℝ => spatialRadius (coordRay x μ s)
  have h_rfun0 : rfun 0 = r := by simp [rfun, hr_def]
  have h_rfun : HasDerivAt rfun ((x μ) / r) 0 :=
    by simpa [rfun, hr_def] using hasDerivAt_spatialRadius_coordRay x μ hμ hr
  have hG : HasDerivAt (fun s => deriv F (rfun s))
      (deriv (deriv F) r * (x μ / r)) 0 :=
    ((hF' r).hasDerivAt).comp 0 h_rfun
  have hH : HasDerivAt (fun s : ℝ => x μ + s) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add _
  have hK : HasDerivAt (fun s => (rfun s)⁻¹) (-(x μ) / r ^ 3) 0 := by
    have := hasDerivAt_inv_spatialRadius x μ hμ hr
    simpa [rfun, hr_def, pow_three, pow_two] using this
  let P : ℝ → ℝ := fun s =>
    partialDeriv_v2 (fun y => F (spatialRadius y)) μ (coordRay x μ s)
  let G := fun s => deriv F (rfun s)
  let H := fun s : ℝ => x μ + s
  let K := fun s => (rfun s)⁻¹
  let g := fun s => G s * H s * K s
  have h_eventually_eq : P =ᶠ[𝓝 (0 : ℝ)] g := by
    have h_ne := eventually_spatialRadius_ne_zero x μ hμ hr
    refine h_ne.mono ?_
    intro s hs
    have hF_at : DifferentiableAt ℝ F (rfun s) := hF _
    have := partialDeriv_radial F (coordRay x μ s) μ hμ hs hF_at
    simp [P, g, G, H, K, rfun, coordRay, hs]
      at this
    simpa using this
  have hP0 : P 0 = g 0 := by
    have hF_at : DifferentiableAt ℝ F r := hF _
    have := partialDeriv_radial F x μ hμ hr hF_at
    simp [P, g, G, H, K, rfun, hr_def, h_rfun0] at this
    simpa [hr_def, h_rfun0] using this
  have h_deriv_g : HasDerivAt g
      (deriv (deriv F) r * (x μ / r) ^ 2
        + deriv F r * (1 / r - (x μ / r) ^ 2 / r)) 0 := by
    have h_prod := (hG.mul hH).mul hK
    have hG0 : G 0 = deriv F r := by simp [G, h_rfun0]
    have hH0 : H 0 = x μ := by simp [H]
    have hK0 : K 0 = 1 / r := by
      have hrpos : 0 < r := spatialRadius_pos_of_ne_zero hr
      simp [K, rfun, hr_def, h_rfun0, inv_eq_one_div, hrpos.ne']
    -- simplify derivative from product rule
    have := h_prod
    simpa [g, G, H, K, hG0, hH0, hK0, hr_def, pow_two, mul_comm, mul_left_comm,
      mul_assoc, sub_eq_add_neg, div_eq_mul_inv] using this
  have h_deriv_P : HasDerivAt P
      (deriv (deriv F) r * (x μ / r) ^ 2
        + deriv F r * (1 / r - (x μ / r) ^ 2 / r)) 0 := by
    exact h_deriv_g.congr_of_mem_nhds h_eventually_eq hP0
  -- By definition of secondDeriv we evaluate this derivative at 0.
  have := h_deriv_P.deriv
  simpa [secondDeriv, P, hr_def, div_eq_mul_inv, pow_two, rfun]
    using this

/-- Laplacian of a radial function equals the classical 3D radial formula. -/
lemma laplacian_of_radial_function
    (F : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hF : Differentiable ℝ F)
    (hF' : Differentiable ℝ fun r => deriv F r)
    (hr : spatialRadius x ≠ 0) :
    laplacian (fun y => F (spatialRadius y)) x =
      deriv (deriv F) (spatialRadius x) +
        (2 / spatialRadius x) * deriv F (spatialRadius x) := by
  classical
  set r := spatialRadius x with hr_def
  have hr0 : r ≠ 0 := by simpa [hr_def] using hr
  have hμ1 := secondDeriv_radial F x 1 (by decide) (by simpa [hr_def] using hr)
      hF hF'
  have hμ2 := secondDeriv_radial F x 2 (by decide) (by simpa [hr_def] using hr)
      hF hF'
  have hμ3 := secondDeriv_radial F x 3 (by decide) (by simpa [hr_def] using hr)
      hF hF'
  have h_sum_sq : (x 1 / r) ^ 2 + (x 2 / r) ^ 2 + (x 3 / r) ^ 2 = 1 := by
    have hr_pos : 0 < r := spatialRadius_pos_of_ne_zero hr0
    have h_norm : r ^ 2 = spatialNormSq x := by
      have := Real.mul_self_sqrt (by exact add_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      simpa [r, spatialRadius, spatialNormSq, pow_two] using this
    have h_sum :
        (x 1 / r) ^ 2 + (x 2 / r) ^ 2 + (x 3 / r) ^ 2
          = (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) / r ^ 2 := by
      simp [pow_two, div_mul_eq_mul_div, add_comm, add_left_comm, add_assoc]
    have h_rhs : (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) / r ^ 2 = 1 := by
      have hr_sq : r ^ 2 ≠ 0 := by
        have : 0 < r ^ 2 := by simpa [pow_two] using sq_pos_of_pos hr_pos
        exact ne_of_gt this
      have := congrArg (fun t => t / r ^ 2) h_norm
      simpa [spatialNormSq, pow_two, hr_def] using this
    simpa [h_sum] using h_rhs
  have h_sum_inv :
      (1 / r - (x 1 / r) ^ 2 / r)
        + (1 / r - (x 2 / r) ^ 2 / r)
        + (1 / r - (x 3 / r) ^ 2 / r)
        = 2 / r := by
    field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc] using congrArg (fun t => (3 : ℝ) / r - t / r) h_sum_sq
  have h_second_sum :
      secondDeriv (fun y => F (spatialRadius y)) 1 1 x
        + secondDeriv (fun y => F (spatialRadius y)) 2 2 x
        + secondDeriv (fun y => F (spatialRadius y)) 3 3 x
        = deriv (deriv F) r + (2 / r) * deriv F r := by
    simp [hμ1, hμ2, hμ3, h_sum_sq, h_sum_inv, pow_two, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc, hr_def, div_eq_mul_inv]
  simpa [laplacian, hr_def] using h_second_sum

/-- Radial profile `C / r`. -/
noncomputable def radialInv (C : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  if spatialRadius x = 0 then 0 else C / spatialRadius x

lemma laplacian_radialInv_zero {C : ℝ} {x : Fin 4 → ℝ}
    (hx : spatialRadius x ≠ 0) :
    laplacian (radialInv C) x = 0 := by
  classical
  have hF : Differentiable ℝ fun r : ℝ => C / r := by
    intro r
    have h := (hasDerivAt_const r C).div (hasDerivAt_id r) (by intro; simp)
    exact h.differentiableAt
  have hF' : Differentiable ℝ fun r : ℝ => deriv (fun s : ℝ => C / s) r := by
    intro r
    have h := (hasDerivAt_const r C).div (hasDerivAt_id r) (by intro; simp)
    exact h.differentiableAt.deriv
  have := laplacian_of_radial_function (fun r => C / r) x hF hF' hx
  have h_deriv : deriv (fun r : ℝ => C / r) = fun r => -C / r^2 := by
    funext r
    have hAt := (hasDerivAt_const r C).div (hasDerivAt_id r) (by intro; simp)
    simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hAt.deriv
  have h_second : deriv (fun r : ℝ => -C / r^2) = fun r => 2 * C / r^3 := by
    funext r
    have hAt :=
      ((hasDerivAt_const r (-C)).mul ((hasDerivAt_id r).pow 2)).inv
        (by intro; simp)
    simpa [h_deriv, pow_two, pow_three, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hAt.deriv
  simp [radialInv, hx, h_deriv, h_second, laplacian_of_radial_function, hx] at this
  simpa [radialInv, hx] using this

end Calculus
end Relativity
end IndisputableMonolith
