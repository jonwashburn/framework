/-
# Half-Plane Poisson Representation Infrastructure

Ported from `riemann-finish/riemann-extra/riemann/no-zeros/rh/academic_framework/HalfPlaneOuterV2.lean`.

This provides the Poisson kernel and integral infrastructure for the right half-plane,
which is key for the Cayley bridge in Route 3.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace HalfPlane

open Complex MeasureTheory Set

/-! ## Section 1: Basic Definitions -/

/-- The right half-plane domain Ω = {s : ℂ | Re s > 1/2} -/
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

/-- Boundary parametrization of the critical line `Re s = 1/2`. -/
@[simp] def boundary (t : ℝ) : ℂ := (1/2 : ℝ) + I * (t : ℂ)

/-- Real part of the boundary parameterization: `re (boundary t) = 1/2`. -/
@[simp] lemma boundary_re (t : ℝ) : (boundary t).re = 1/2 := by simp [boundary]

/-- Imaginary part of the boundary parameterization: `im (boundary t) = t`. -/
@[simp] lemma boundary_im (t : ℝ) : (boundary t).im = t := by simp [boundary]

/-- Off-zeros domain for ξ on Ω, excluding points where ξ vanishes. -/
def offZeros (ξ : ℂ → ℂ) : Set ℂ := {z | z ∈ Ω ∧ ξ z ≠ 0}

/-- Off-zeros domain for `xiLagarias` on Ω. -/
def offXi : Set ℂ := offZeros xiLagarias

lemma offXi_subset_Ω : offXi ⊆ Ω := fun z hz => hz.1

/-! ## Section 2: Poisson Kernel -/

/-- The Poisson kernel for the right half‑plane.
    P_z(t) = (1/π) · (Re z - 1/2) / ((Re z - 1/2)² + (t - Im z)²) -/
@[simp] def poissonKernel (z : ℂ) (t : ℝ) : ℝ :=
  let a := z.re - 1/2
  let b := z.im
  (1 / Real.pi) * (a / (a^2 + (t - b)^2))

/-- Non-negativity of the Poisson kernel for z ∈ Ω -/
lemma poissonKernel_nonneg {z : ℂ} (hz : z ∈ Ω) (t : ℝ) :
    0 ≤ poissonKernel z t := by
  unfold poissonKernel Ω at *
  simp only [Set.mem_setOf_eq] at hz
  have ha : 0 < z.re - 1/2 := sub_pos.mpr hz
  have hdenom : 0 < (z.re - 1/2)^2 + (t - z.im)^2 := by
    apply add_pos_of_pos_of_nonneg
    · exact pow_pos ha 2
    · exact sq_nonneg _
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
    (div_nonneg ha.le hdenom.le)

/-! ## Section 3: Poisson Integral -/

/-- Poisson integral: reconstructs interior values from boundary data -/
@[simp] def poissonIntegral (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, u t * poissonKernel z t

/-- Poisson integral of the zero boundary function. -/
@[simp] lemma poissonIntegral_zero (z : ℂ) :
    poissonIntegral (fun _ => (0 : ℝ)) z = 0 := by
  simp [poissonIntegral]

/-! ## Section 4: Poisson Representation -/

/-- A function F has a Poisson representation on S if:
    1. S ⊆ Ω
    2. F is analytic on S
    3. The boundary integral is integrable
    4. Re(F z) = Poisson integral of boundary Re(F) -/
structure HasPoissonRepOn (F : ℂ → ℂ) (S : Set ℂ) : Prop where
  subset : S ⊆ Ω
  analytic : AnalyticOn ℂ F S
  integrable : ∀ z ∈ S, Integrable (fun t : ℝ => (F (boundary t)).re * poissonKernel z t)
  formula : ∀ z ∈ S, (F z).re = poissonIntegral (fun t => (F (boundary t)).re) z

/-- Poisson real‑part identity for `F` on a subset `S ⊆ Ω`. -/
def HasPoissonReEqOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, (F z).re = poissonIntegral (fun t : ℝ => (F (boundary t)).re) z

/-- A Poisson representation implies the real-part identity. -/
lemma hasPoissonReEqOn_of_hasPoissonRepOn (F : ℂ → ℂ) {S : Set ℂ}
    (hRep : HasPoissonRepOn F S) : HasPoissonReEqOn F S :=
  fun z hz => hRep.formula z hz

/-! ## Section 5: Outer Functions -/

/-- An outer function on Ω: analytic and non-vanishing -/
structure IsOuter (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonvanishing : ∀ s ∈ Ω, O s ≠ 0

/-- Boundary modulus equality: |O| = |F| on the critical line -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, abs (O (boundary t)) = abs (F (boundary t))

/-! ## Section 6: Cayley Adapters -/

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def fromDisk (w : ℂ) : ℂ := 1 / (1 - w)

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (boundary t)

/-- Points of Ω are nonzero: if `Re z > 1/2` then `z ≠ 0`. -/
lemma memΩ_ne_zero {z : ℂ} (hz : z ∈ Ω) : z ≠ 0 := by
  intro h0
  have hzRe : (1/2 : ℝ) < z.re := by
    simpa [Ω, Set.mem_setOf_eq] using hz
  have hlt : (1/2 : ℝ) < 0 := by simpa [h0, Complex.zero_re] using hzRe
  exact (not_lt.mpr (by norm_num : (0 : ℝ) ≤ (1/2 : ℝ))) hlt

/-- Algebraic identity: for any nonzero `z`, `fromDisk (toDisk z) = z`. -/
lemma fromDisk_toDisk_of_ne {z : ℂ} (hz : z ≠ 0) : fromDisk (toDisk z) = z := by
  have h1 : (1 : ℂ) - (z - 1) / z = (1 : ℂ) / z := by
    field_simp [toDisk, hz]
  calc
    fromDisk (toDisk z)
        = 1 / (1 - (z - 1) / z) := by simp [fromDisk, toDisk]
    _ = 1 / ((1 : ℂ) / z) := by simpa [h1]
    _ = z := by field_simp [hz]

/-- On the right half-plane Ω, the Cayley maps cancel. -/
lemma fromDisk_toDisk_of_mem_Ω {z : ℂ} (hz : z ∈ Ω) :
    fromDisk (toDisk z) = z :=
  fromDisk_toDisk_of_ne (memΩ_ne_zero hz)

/-- Boundary points are nonzero. -/
lemma boundary_ne_zero (t : ℝ) : boundary t ≠ 0 := by
  intro h0
  have hRe0 : (boundary t).re = 0 := by
    simpa using congrArg Complex.re h0
  have : (1/2 : ℝ) = 0 := by
    simpa [boundary_re] using hRe0
  exact (by norm_num : (1/2 : ℝ) ≠ 0) this

/-- Boundary transport under the Cayley map. -/
@[simp] lemma fromDisk_boundaryToDisk (t : ℝ) :
    fromDisk (boundaryToDisk t) = boundary t := by
  simpa [boundaryToDisk] using fromDisk_toDisk_of_ne (boundary_ne_zero t)

/-! ## Section 7: Key Bridge Theorem -/

/-- Boundary identification along Cayley: `F ∘ boundary = H ∘ boundaryToDisk`. -/
def EqOnBoundary (F H : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, F (boundary t) = H (boundaryToDisk t)

/-- Cayley kernel transport on `S`: Poisson of pullback boundary real part equals `(H ∘ toDisk).re`. -/
def CayleyKernelTransportOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    poissonIntegral (fun t : ℝ => (H (boundaryToDisk t)).re) z
      = (H (toDisk z)).re

/-- Half‑plane real‑part identity on `S` from interior/boundary matches and kernel transport. -/
theorem hasPoissonReEqOn_from_cayley
    (F H : ℂ → ℂ) {S : Set ℂ}
    (hEqInterior : Set.EqOn F (fun z => H (toDisk z)) S)
    (hEqBoundary : EqOnBoundary F H)
    (hKernel : CayleyKernelTransportOn H S)
    : HasPoissonReEqOn F S := by
  intro z hzS
  have h1 : (F z).re = (H (toDisk z)).re := by
    simpa using congrArg Complex.re (hEqInterior hzS)
  have hIntgEq :
      (fun t : ℝ => (F (boundary t)).re)
        = (fun t : ℝ => (H (boundaryToDisk t)).re) := by
    funext t
    simpa using congrArg Complex.re (hEqBoundary t)
  have hPI :
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
        = (H (toDisk z)).re := by
    calc
      poissonIntegral (fun t : ℝ => (F (boundary t)).re) z
          = poissonIntegral (fun t : ℝ => (H (boundaryToDisk t)).re) z := by
            exact congrArg (fun f => poissonIntegral f z) hIntgEq
      _ = (H (toDisk z)).re :=
            hKernel z hzS
  simpa [h1] using hPI.symm

end HalfPlane

end ExplicitFormula
end RiemannRecognitionGeometry
