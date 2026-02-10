import Mathlib
import IndisputableMonolith.Measurement.RecognitionAngle.ActionSmallAngle

/-!
# DNA Geometry under Blind-Cone Constraints: Kinematics and Site Angles

Formulation-only module: defines helix kinematics (κ, τ, tanψ) and the local
angle between successive recognition sites as seen from an observer point.
-/

noncomputable section

open scoped Real

namespace IndisputableMonolith
namespace BiophaseIntegration

namespace RecognitionDNA

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Idealized circular helix parameters. `a` is axial spacing between successive sites. -/
structure Helix where
  R : ℝ
  P : ℝ
  a : ℝ
  hR : 0 < R
  hP : 0 < P
  ha : 0 < a

/-- Curvature of a circular helix. -/
def curvature (h : Helix) : ℝ :=
  let denom := (h.R ^ 2 + (h.P / (2 * Real.pi)) ^ 2)
  h.R / denom

/-- Torsion of a circular helix. -/
def torsion (h : Helix) : ℝ :=
  let denom := (h.R ^ 2 + (h.P / (2 * Real.pi)) ^ 2)
  (h.P / (2 * Real.pi)) / denom

/-- The torsion-to-curvature ratio `tan ψ = τ/κ = P/(2πR)`. -/
def tanPsi (h : Helix) : ℝ :=
  (h.P / (2 * Real.pi)) / h.R

/-- Parametric helix curve. Parameter `t` is arc-parameterized up to scale. -/
def helixPoint (h : Helix) (t : ℝ) : R3 :=
  let u := t * (2 * Real.pi / h.P)
  ![h.R * Real.cos u, h.R * Real.sin u, t]

/-- Discrete site positions separated by axial spacing `a`. -/
def site (h : Helix) (k : ℤ) : R3 :=
  helixPoint h (k.toReal * h.a)

open IndisputableMonolith.Measurement.RecognitionAngle
open IndisputableMonolith.Measurement.RecognitionAngle (angleOK)

/-- Local recognition angle between successive sites from observer `x`. -/
def siteAngle (x : R3) (h : Helix) (k : ℤ) : ℝ :=
  let y₁ := site h k
  let y₂ := site h (k + 1)
  angleAt x y₁ y₂

/-- Site pair convenience. -/
def sitePair (h : Helix) (k : ℤ) : R3 × R3 := (site h k, site h (k + 1))

/-- Schema: threshold on `siteAngle` is equivalent to `angleOK` for the site pair. -/
theorem angleOK_of_siteAngle_threshold {x : R3} {h : Helix} {k : ℤ} {Amax : ℝ} :
    siteAngle x h k ≥ thetaMin Amax →
    angleOK x (site h k) (site h (k + 1)) Amax := by
  intro hθ
  dsimp [siteAngle, angleOK]
  simpa

/-- Feasibility of a DNA recognition step under temporal gating given angular threshold. -/
theorem dna_step_feasible_if_threshold_and_time
    {x : R3} (h : Helix) (k : ℤ) {Amax : ℝ}
    {p : IndisputableMonolith.Measurement.RecognitionAngle.EightTickParams}
    (hθ : siteAngle x h k ≥ thetaMin Amax)
    (hslot : ∃ n : ℤ, IndisputableMonolith.Measurement.RecognitionAngle.timeOK n p) :
    ∃ n : ℤ, IndisputableMonolith.Measurement.RecognitionAngle.feasible
      x (site h k) (site h (k + 1)) Amax p n := by
  have hgeom : angleOK x (site h k) (site h (k + 1)) Amax := by
    exact angleOK_of_siteAngle_threshold (x := x) (h := h) (k := k) (Amax := Amax) hθ
  rcases hslot with ⟨n, hn⟩
  exact ⟨n, And.intro hgeom hn⟩

end RecognitionDNA

end BiophaseIntegration
end IndisputableMonolith
