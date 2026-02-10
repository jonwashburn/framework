import IndisputableMonolith.OctaveKernel.Instances.SpatialLattice3D
import Mathlib

/-!
# OctaveKernel.Instances.SpatialCouplingWeights

This module **pins down** the face/edge coupling weights by the standard
"isotropy + unitarity/normalization" move:

- Treat the 6 face directions and 12 edge directions as two isotropic channel-families.
- A unitary 2×2 mixing on the **normalized** face-average and edge-average modes
  is parameterized by a single angle `θ`.
- When expanded back to per-direction weights, this forces the normalization law
  \( 6|wFace|^2 + 12|wEdge|^2 = 1 \).

We also provide a **canonical** choice `θ₀ = π/12`, motivated by the RS "12-channel
interference amplitude" marker `sin(π/12)` present in the book.

Note: This file pins down *weights*; proving global energy conservation of a full
multi-directional wave update requires an explicit directional-channel state.
Here we provide the normalized weights that are compatible with such a unitary design.
-/

namespace IndisputableMonolith
namespace OctaveKernel
namespace Instances

open scoped Real

/-! ## Derived weights from a unitary 2×2 mixing angle -/

/-- Face-coupling weight derived from mixing angle `θ`.

Interpretation: `cos θ` is the amplitude share in the normalized **face-average** mode;
dividing by `√6` spreads it uniformly over 6 face channels. -/
noncomputable def wFace (θ : ℝ) : ℂ :=
  Complex.ofReal (Real.cos θ / Real.sqrt 6)

/-- Edge-coupling weight derived from mixing angle `θ`.

Interpretation: `sin θ` is the amplitude share in the normalized **edge-average** mode;
dividing by `√12` spreads it uniformly over 12 edge channels. -/
noncomputable def wEdge (θ : ℝ) : ℂ :=
  Complex.ofReal (Real.sin θ / Real.sqrt 12)

/-- The forced normalization (unitarity) law for the derived weights. -/
theorem weights_normalized (θ : ℝ) :
    (6 : ℝ) * ‖wFace θ‖ ^ 2 + (12 : ℝ) * ‖wEdge θ‖ ^ 2 = 1 := by
  -- In ℂ, `‖(r : ℂ)‖ = |r|`. Use this to reduce to real trig + `cos²+sin²=1`.
  have hs6 : (0 : ℝ) ≤ 6 := by norm_num
  have hs12 : (0 : ℝ) ≤ 12 := by norm_num
  have habs_sqrt6 : |Real.sqrt (6 : ℝ)| ^ 2 = 6 := by
    -- |√6| = √6 (nonnegative), and (√6)^2 = 6
    have : (Real.sqrt (6 : ℝ)) ^ 2 = 6 := by
      simpa [pow_two] using (Real.sq_sqrt hs6)
    simpa [abs_of_nonneg (Real.sqrt_nonneg _), this]
  have habs_sqrt12 : |Real.sqrt (12 : ℝ)| ^ 2 = 12 := by
    have : (Real.sqrt (12 : ℝ)) ^ 2 = 12 := by
      simpa [pow_two] using (Real.sq_sqrt hs12)
    simpa [abs_of_nonneg (Real.sqrt_nonneg _), this]

  -- Reduce the norms to abs-values on ℝ.
  calc
    (6 : ℝ) * ‖wFace θ‖ ^ 2 + (12 : ℝ) * ‖wEdge θ‖ ^ 2
        = (6 : ℝ) * (|Real.cos θ| / |Real.sqrt (6 : ℝ)|) ^ 2
            + (12 : ℝ) * (|Real.sin θ| / |Real.sqrt (12 : ℝ)|) ^ 2 := by
              simp [wFace, wEdge, Complex.norm_real, Real.norm_eq_abs, pow_two,
                -Complex.ofReal_cos, -Complex.ofReal_sin]
    _ = (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 := by
          -- (|x|/|√n|)^2 = x^2 / n
          -- use `div_pow` and `abs_mul_abs_self : |x|*|x| = x*x`.
          have hcos : |Real.cos θ| ^ 2 = (Real.cos θ) ^ 2 := by
            simp [pow_two, abs_mul_abs_self]
          have hsin : |Real.sin θ| ^ 2 = (Real.sin θ) ^ 2 := by
            simp [pow_two, abs_mul_abs_self]
          -- Apply these reductions and the sqrt identities.
          simp [div_pow, hcos, hsin, habs_sqrt6, habs_sqrt12, -Real.cos_sq_add_sin_sq]
          ring_nf
    _ = 1 := by
          -- cos^2 + sin^2 = 1
          simpa using Real.cos_sq_add_sin_sq θ

/-! ## Canonical choice: θ₀ = π/12 -/

/-- Canonical 12-channel mixing angle.

Motivation: RS highlights `sin(π/12)` as the 12-channel voxel-interference amplitude. -/
noncomputable def θ₀ : ℝ := Real.pi / 12

noncomputable def wFace₀ : ℂ := wFace θ₀
noncomputable def wEdge₀ : ℂ := wEdge θ₀

theorem weights_normalized_θ₀ :
    (6 : ℝ) * ‖wFace₀‖ ^ 2 + (12 : ℝ) * ‖wEdge₀‖ ^ 2 = 1 := by
  simpa [wFace₀, wEdge₀, θ₀] using weights_normalized (θ := θ₀)

/-! ## Ready-to-use canonical stencil on the 3D torus lattice -/

/-- Canonical face+edge stencil on the `Pos N` torus using the pinned-down weights. -/
noncomputable def torusFacePlusEdgeStencil₀ (N : ℕ) :
    MeaningfulVoxelField.SpatialStencil (Pos N) :=
  torusFacePlusEdgeStencil (N := N) (wFace₀) (wEdge₀)

/-- The combined (faces+edges) stencil has unit-normalized total weight power.

This is the explicit “isotropy + normalization” constraint in stencil form:
\(\sum_d ‖w(d)‖^2 = 1\). -/
theorem torusFacePlusEdgeStencil_weightPower (N : ℕ) (θ : ℝ) :
    let S := torusFacePlusEdgeStencil (N := N) (wFace θ) (wEdge θ)
    (∑ d : S.Dir, ‖S.weight d‖ ^ 2) = 1 := by
  classical
  intro S
  -- `S.Dir = Sum (Fin 6) (Fin 12)` and the weight is constant on each side,
  -- so the total weight power is `6*‖wFace‖^2 + 12*‖wEdge‖^2`.
  have hsum :
      (∑ d : S.Dir, ‖S.weight d‖ ^ 2) =
        (6 : ℝ) * ‖wFace θ‖ ^ 2 + (12 : ℝ) * ‖wEdge θ‖ ^ 2 := by
    -- First unfold the `let`-bound stencil so its `Dir` and `weight` become definitional.
    dsimp [S]
    -- Now split the sum over `Sum (Fin 6) (Fin 12)` and evaluate the constant sums.
    simp [torusFacePlusEdgeStencil, MeaningfulVoxelField.VoxelLattice.facePlusEdgeStencil,
      Finset.sum_disjSum, pow_two, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  -- Conclude using the derived normalization theorem.
  simpa [hsum] using weights_normalized (θ := θ)

/-- Canonical θ₀ = π/12 specialization. -/
theorem torusFacePlusEdgeStencil₀_weightPower (N : ℕ) :
    let S := torusFacePlusEdgeStencil₀ (N := N)
    (∑ d : S.Dir, ‖S.weight d‖ ^ 2) = 1 := by
  intro S
  -- Unfold the canonical stencil and apply the generic theorem at θ₀.
  simpa [torusFacePlusEdgeStencil₀, wFace₀, wEdge₀, θ₀] using
    (torusFacePlusEdgeStencil_weightPower (N := N) (θ := θ₀))

end Instances
end OctaveKernel
end IndisputableMonolith
