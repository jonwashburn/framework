/-
# Outer Functions and Schur Bridge

Ported from `riemann-finish/riemann-extra/riemann/no-zeros/rh/RS/`:
- `Det2Outer.lean` - Outer function construction
- `SchurGlobalization.lean` - Schur function infrastructure
- `OffZerosBridge.lean` - Off-zeros bridge

This provides the infrastructure needed to fill the hard sorries in Route 3.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner
import RiemannRecognitionGeometry.ExplicitFormula.HalfPlanePoisson
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias
import RiemannRecognitionGeometry.ExplicitFormula.Cayley

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace OuterSchur

open Complex HalfPlane Set

/-! ## Section 1: Domain Definitions -/

/-- Zero set of a function. -/
def Z (f : ℂ → ℂ) : Set ℂ := {s | f s = 0}

/-- Nonvanishing of a function on a set. -/
def IsNonzeroOn (S : Set ℂ) (f : ℂ → ℂ) : Prop := ∀ ⦃s⦄, s ∈ S → f s ≠ 0

/-- Ω is open. -/
lemma isOpen_Ω : IsOpen Ω := by
  simpa [Ω, Set.preimage, Set.mem_setOf_eq] using
    (isOpen_Ioi.preimage continuous_re)

/-! ## Section 2: Schur Functions -/

/-- Schur predicate on a set: |Θ(z)| ≤ 1 for all z ∈ S. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, Complex.abs (Θ z) ≤ 1

/-- Monotonicity of the Schur predicate under set inclusion. -/
lemma IsSchurOn.mono {Θ : ℂ → ℂ} {S T : Set ℂ}
    (h : IsSchurOn Θ S) (hTS : T ⊆ S) : IsSchurOn Θ T := by
  intro z hz; exact h z (hTS hz)

/-- Default constant Schur function on Ω. -/
def Theta_schur_default : ℂ → ℂ := fun _ => (1 : ℂ)

/-- The constant function 1 is Schur on Ω. -/
lemma Theta_schur_default_isSchur : IsSchurOn Theta_schur_default Ω := by
  intro z _; simp [Theta_schur_default]

/-! ## Section 3: Cayley Transform → Schur (Key Bridge) -/

/-- If Re(F z) ≥ 0 on S and F z + 1 ≠ 0 on S, then the Cayley transform (F-1)/(F+1) is Schur on S.

This is the key bridge lemma from riemann-finish/SchurGlobalization.lean.
-/
theorem schur_of_cayley_re_nonneg_on
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re)
    (hDen : ∀ z ∈ S, F z + 1 ≠ 0) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  intro z hz
  have hden : F z + 1 ≠ 0 := hDen z hz
  have hRez : 0 ≤ (F z).re := hRe z hz
  -- Goal: |(w-1)/(w+1)| ≤ 1 when Re w ≥ 0 and w ≠ -1
  -- Reduce to |w-1| ≤ |w+1|
  set x : ℝ := (F z).re with hx
  set y : ℝ := (F z).im with hy
  have hxplus : (F z + 1).re = x + 1 := by simp [hx]
  have hyplus : (F z + 1).im = y := by simp [hy]
  have hxminus : (F z - 1).re = x - 1 := by simp [hx]
  have hyminus : (F z - 1).im = y := by simp [hy]
  have hdiff : (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2 = 4 * x := by
    have h1s : (Complex.abs (F z + 1)) ^ 2 = (x + 1) * (x + 1) + y * y := by
      rw [Complex.sq_abs]
      simp only [Complex.normSq_apply, hxplus, hyplus, pow_two]
    have h2s : (Complex.abs (F z - 1)) ^ 2 = (x - 1) * (x - 1) + y * y := by
      rw [Complex.sq_abs]
      simp only [Complex.normSq_apply, hxminus, hyminus, pow_two]
    have : ((x + 1) * (x + 1) + y * y) - ((x - 1) * (x - 1) + y * y) = 4 * x := by ring
    simp [h1s, h2s, this]
  have hnonneg : 0 ≤ (Complex.abs (F z + 1)) ^ 2 - (Complex.abs (F z - 1)) ^ 2 := by
    have hxnonneg : 0 ≤ x := by simpa [hx] using hRez
    have : 0 ≤ 4 * x := mul_nonneg (by norm_num) hxnonneg
    simp [hdiff, this]
  have hle_sq : (Complex.abs (F z - 1)) ^ 2 ≤ (Complex.abs (F z + 1)) ^ 2 :=
    sub_nonneg.mp hnonneg
  -- Monotonicity of sqrt gives |w-1| ≤ |w+1|
  have hle : Complex.abs (F z - 1) ≤ Complex.abs (F z + 1) := by
    have : Real.sqrt ((Complex.abs (F z - 1)) ^ 2) ≤ Real.sqrt ((Complex.abs (F z + 1)) ^ 2) :=
      Real.sqrt_le_sqrt hle_sq
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Conclude |(w-1)/(w+1)| ≤ 1
  have hden_pos : 0 < Complex.abs (F z + 1) := Complex.abs.pos_iff.mpr hden
  have hmul : Complex.abs (F z - 1) / Complex.abs (F z + 1)
      ≤ Complex.abs (F z + 1) / Complex.abs (F z + 1) :=
    div_le_div_of_nonneg_right hle (Complex.abs.nonneg _)
  have hdiv_le_one : Complex.abs (F z - 1) / Complex.abs (F z + 1) ≤ 1 := by
    simpa [div_self (ne_of_gt hden_pos)] using hmul
  -- Final step: rewrite |(F-1)/(F+1)| as |F-1|/|F+1|
  simpa [map_div₀] using hdiv_le_one

/-! ## Section 4: Outer Function Interface -/

/-- Half‑plane outer interface: `O` analytic and zero‑free on Ω. -/
structure OuterHalfPlane (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonzero : ∀ {s}, s ∈ Ω → O s ≠ 0

/-- Concrete boundary‑modulus equality on Re s = 1/2. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, Complex.abs (O (boundary t)) = Complex.abs (F (boundary t))

/-- Statement‑level constructor: an outer `O` on Ω whose boundary modulus equals
`|det2/ξ|` on the boundary line Re s = 1/2. -/
def OuterHalfPlane.ofModulus (det2 ξ : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterHalfPlane O ∧ BoundaryModulusEq O (fun s => det2 s / ξ s)

/-- Exponential is never zero: an outer given by `exp ∘ H` is zero-free on any set. -/
lemma outer_exp_nonzeroOn {S : Set ℂ} (H : ℂ → ℂ) :
    IsNonzeroOn S (fun s => Complex.exp (H s)) := by
  intro s _; exact Complex.exp_ne_zero (H s)

/-! ## Section 5: Off-Zeros Bridge -/

/-- Local data at a zero ρ suitable to build the assignment for the off-zeros bridge. -/
structure LocalData (Θ : ℂ → ℂ) (ρ : ℂ) where
  U : Set ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hρU : ρ ∈ U
  hIso : (U ∩ {z | xiLagarias z = 0}) = ({ρ} : Set ℂ)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

/-- Stable alias: a local chooser supplies `LocalData Θ ρ` at each ξ‑zero ρ in Ω. -/
def LocalChooser (Θ : ℂ → ℂ) : Type :=
  ∀ ρ : ℂ, ρ ∈ Ω → xiLagarias ρ = 0 → LocalData Θ ρ

/-- Assignment on ξ-zeros: for each zero ρ ∈ Ω, bundle the removability data. -/
structure AssignShape (Θ : ℂ → ℂ) where
  assign : LocalChooser Θ

/-! ## Section 6: Zeta-Schur Decomposition -/

/-- Non-circular, off-zeros ξ→Schur bridge on Ω.

`hξeq_off` only asserts the ξ = Θ / N identity off the zero set of ξ (so division is legal),
and `hN_nonzero_off` only requires nonvanishing of `N` off the zeros of ξ. This avoids
encoding the target theorem (nonvanishing of ξ on Ω) in the interface. -/
structure XiSchurDecompositionOffZeros where
  Θ : ℂ → ℂ
  N : ℂ → ℂ
  hΘSchur : IsSchurOn Θ Ω
  hNanalytic : AnalyticOn ℂ N Ω
  hξeq_off : ∀ z ∈ (Ω \ {z | xiLagarias z = 0}), xiLagarias z = Θ z / N z
  hN_nonzero_off : ∀ z ∈ (Ω \ {z | xiLagarias z = 0}), N z ≠ 0

/-! ## Section 7: Pinch Field Construction -/

/-- Paper choice: define `J_pinch := det₂ / (O · ξ)` on Ω.

This is the key arithmetic/outer field for the Route 3 bridge.
When the outer O has boundary modulus |O| = |det2/ξ|, the pinch field J_pinch
has unit modulus on the boundary. -/
def J_pinch (det2 O ξ : ℂ → ℂ) (s : ℂ) : ℂ :=
  det2 s / (O s * ξ s)

/-- The pinch field `F := 2 · J_pinch det2 O ξ`. -/
@[simp] def F_pinch (det2 O ξ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) * J_pinch det2 O ξ z

/-- On the boundary line Re s = 1/2, assuming the boundary modulus equality
`|O(1/2+it)| = |det2/ξ(1/2+it)|`, the pinch field has unit modulus:
`|J_pinch det2 O ξ (1/2+it)| = 1`, provided `O(1/2+it)` and `ξ(1/2+it)` are nonzero. -/
lemma boundary_abs_J_pinch_eq_one
    {det2 O ξ : ℂ → ℂ}
    (hBME : BoundaryModulusEq O (fun s => det2 s / ξ s))
    (t : ℝ)
    (hO : O (boundary t) ≠ 0)
    (hXi : ξ (boundary t) ≠ 0) :
    Complex.abs (J_pinch det2 O ξ (boundary t)) = 1 := by
  set z : ℂ := boundary t
  have hOabs : Complex.abs (O z) = Complex.abs (det2 z / ξ z) := hBME t
  -- |O|·|ξ| = |det2|
  have hprod : Complex.abs (O z) * Complex.abs (ξ z) = Complex.abs (det2 z) := by
    calc
      Complex.abs (O z) * Complex.abs (ξ z)
          = Complex.abs (det2 z / ξ z) * Complex.abs (ξ z) := by rw [hOabs]
      _ = Complex.abs ((det2 z / ξ z) * (ξ z)) := by rw [← Complex.abs.map_mul]
      _ = Complex.abs (det2 z) := by
        have hxinv : (ξ z)⁻¹ * (ξ z) = (1 : ℂ) := inv_mul_cancel₀ hXi
        have hdiv_mul : (det2 z / ξ z) * (ξ z) = det2 z := by
          field_simp [hXi]
        rw [hdiv_mul]
  -- |J| = |det2| / (|O|·|ξ|) = 1
  have hJabs : Complex.abs (J_pinch det2 O ξ z)
      = Complex.abs (det2 z) / (Complex.abs (O z) * Complex.abs (ξ z)) := by
    simp only [J_pinch]
    rw [map_div₀, Complex.abs.map_mul]
  have hden_pos : 0 < Complex.abs (O z) * Complex.abs (ξ z) := by
    exact mul_pos (Complex.abs.pos_iff.mpr hO) (Complex.abs.pos_iff.mpr hXi)
  have hden_ne : (Complex.abs (O z) * Complex.abs (ξ z)) ≠ 0 := ne_of_gt hden_pos
  rw [hJabs, ← hprod, div_self hden_ne]

/-- Uniform boundary bound for the real part of the pinch field:
`|(F_pinch det2 O ξ (boundary t)).re| ≤ 2` for all real `t`. -/
lemma F_pinch_boundary_bound
    {det2 O ξ : ℂ → ℂ}
    (hBME : BoundaryModulusEq O (fun s => det2 s / ξ s))
    (t : ℝ) :
    |((F_pinch det2 O ξ) (boundary t)).re| ≤ (2 : ℝ) := by
  set z : ℂ := boundary t
  -- Either the denominator vanishes or not; in both cases `|J| ≤ 1`.
  have hJ_le_one : Complex.abs (J_pinch det2 O ξ z) ≤ 1 := by
    by_cases hO0 : O z = 0
    · -- denominator zero ⇒ J = 0
      have hJ0 : J_pinch det2 O ξ z = 0 := by simp [J_pinch, hO0]
      rw [hJ0, Complex.abs.map_zero]; norm_num
    · by_cases hXi0 : ξ z = 0
      · have hJ0 : J_pinch det2 O ξ z = 0 := by simp [J_pinch, hXi0]
        rw [hJ0, Complex.abs.map_zero]; norm_num
      · have h1 : Complex.abs (J_pinch det2 O ξ z) = 1 :=
          boundary_abs_J_pinch_eq_one hBME t hO0 hXi0
        rw [h1]
  -- |F.re| = |2 · J.re| ≤ 2 · |J| ≤ 2
  have hFre : ((F_pinch det2 O ξ) z).re = 2 * (J_pinch det2 O ξ z).re := by
    simp only [F_pinch, mul_re]
    have h2re : (2 : ℂ).re = 2 := rfl
    have h2im : (2 : ℂ).im = 0 := rfl
    rw [h2re, h2im]
    ring
  have habs_re_le : |(J_pinch det2 O ξ z).re| ≤ Complex.abs (J_pinch det2 O ξ z) :=
    Complex.abs_re_le_abs (J_pinch det2 O ξ z)
  calc
    |((F_pinch det2 O ξ) z).re| = |2 * (J_pinch det2 O ξ z).re| := by rw [hFre]
    _ = 2 * |(J_pinch det2 O ξ z).re| := by rw [abs_mul]; simp
    _ ≤ 2 * Complex.abs (J_pinch det2 O ξ z) := by
        exact mul_le_mul_of_nonneg_left habs_re_le (by norm_num)
    _ ≤ 2 * 1 := by exact mul_le_mul_of_nonneg_left hJ_le_one (by norm_num)
    _ = 2 := by ring

/-! ## Section 8: Poisson Transport Theorem (Key!) -/

/-- Boundary positivity condition (P+) -/
def BoundaryPositive (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (F (boundary t)).re

/-- Poisson representation on the full half-plane Ω -/
structure HasPoissonRep (F : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ F Ω
  integrable : ∀ z ∈ Ω, MeasureTheory.Integrable (fun t => (F (boundary t)).re * HalfPlane.poissonKernel z t)
  formula : ∀ z ∈ Ω, (F z).re = HalfPlane.poissonIntegral (fun t => (F (boundary t)).re) z

/-- **KEY THEOREM**: Poisson transport - boundary positivity implies interior positivity.

This is the core mechanism of the Route 3 bridge. If F has a Poisson representation
and the boundary values are nonnegative almost everywhere, then interior values
are nonnegative everywhere on Ω.

Ported from riemann-finish/academic_framework/HalfPlaneOuterV2.lean. -/
theorem poissonTransport {F : ℂ → ℂ} (hRep : HasPoissonRep F) :
    BoundaryPositive F → ∀ z ∈ Ω, 0 ≤ (F z).re := by
  intro hBoundary z hz
  -- Use the Poisson representation
  rw [hRep.formula z hz]
  unfold HalfPlane.poissonIntegral
  -- The integral of non-negative functions is non-negative
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (HalfPlane.poissonKernel_nonneg hz t)

/-- Subset Poisson representation (for domains with excluded singularities).
Uses a plain predicate to avoid Prop-structure generation issues. -/
def HasPoissonRepOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  (S ⊆ Ω) ∧
  (AnalyticOn ℂ F S) ∧
  (∀ z ∈ S, MeasureTheory.Integrable (fun t => (F (boundary t)).re * HalfPlane.poissonKernel z t)) ∧
  (∀ z ∈ S, (F z).re = HalfPlane.poissonIntegral (fun t => (F (boundary t)).re) z)

/-- Restrict a global half‑plane Poisson representation to any subset `S ⊆ Ω`. -/
theorem repOn_of_rep_subset {F : ℂ → ℂ} {S : Set ℂ}
    (hRep : HasPoissonRep F) (hS : S ⊆ Ω) : HasPoissonRepOn F S :=
  ⟨hS, hRep.analytic.mono hS, fun z hzS => hRep.integrable z (hS hzS),
   fun z hzS => hRep.formula z (hS hzS)⟩

/-- Builder: obtain a subset half‑plane Poisson representation from
an a priori real‑part Poisson identity on `S ⊆ Ω`, together with analyticity
and the required integrability of the boundary integrand. -/
theorem repOn_from_reEqOn {F : ℂ → ℂ} {S : Set ℂ}
    (hS : S ⊆ Ω)
    (hA : AnalyticOn ℂ F S)
    (hI : ∀ z ∈ S, MeasureTheory.Integrable (fun t => (F (boundary t)).re * HalfPlane.poissonKernel z t))
    (hReEqOn : ∀ z ∈ S, (F z).re = HalfPlane.poissonIntegral (fun t => (F (boundary t)).re) z)
    : HasPoissonRepOn F S :=
  ⟨hS, hA, hI, hReEqOn⟩

/-- Transport on subsets -/
theorem poissonTransportOn {F : ℂ → ℂ} {S : Set ℂ} (hRep : HasPoissonRepOn F S) :
    BoundaryPositive F → ∀ z ∈ S, 0 ≤ (F z).re := by
  obtain ⟨hSΩ, _, _, hform⟩ := hRep
  intro hBoundary z hz
  rw [hform z hz]
  unfold HalfPlane.poissonIntegral
  apply MeasureTheory.integral_nonneg_of_ae
  have hzΩ : z ∈ Ω := hSΩ hz
  filter_upwards [hBoundary] with t ht
  exact mul_nonneg ht (HalfPlane.poissonKernel_nonneg hzΩ t)

/-! ## Section 9: Cayley Transform Construction -/

/-- Cayley transform: maps a function J to Θ = (2J - 1)/(2J + 1).

When Re(2J) ≥ 0, this gives a Schur function (|Θ| ≤ 1) by `schur_of_cayley_re_nonneg_on`. -/
def Theta_of_J (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ((2 : ℂ) * J z - 1) / ((2 : ℂ) * J z + 1)

/-- Θ is Schur when Re(2J) ≥ 0 and 2J + 1 ≠ 0. -/
theorem Theta_Schur_of_Re_nonneg_on (J : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ ((2 : ℂ) * J z).re) :
    IsSchurOn (Theta_of_J J) S := by
  -- Theta_of_J J z = (2Jz - 1)/(2Jz + 1) = (F - 1)/(F + 1) where F = 2J
  -- This is exactly schur_of_cayley_re_nonneg_on with F = 2J
  have hDen : ∀ z ∈ S, (2 : ℂ) * J z + 1 ≠ 0 := by
    intro z hz h
    -- If 2J z + 1 = 0, then 2J z = -1, so Re(2J z) = -1 < 0
    have h_neg : (2 : ℂ) * J z = -1 := by
      have := eq_neg_of_add_eq_zero_left h
      simp at this
      exact this
    have hRe_neg : ((2 : ℂ) * J z).re = (-1 : ℂ).re := congrArg Complex.re h_neg
    simp only [neg_re, one_re] at hRe_neg
    linarith [hRe z hz]
  have hSchur := schur_of_cayley_re_nonneg_on (fun z => (2 : ℂ) * J z) S hRe hDen
  -- Now show Theta_of_J J = (2J - 1)/(2J + 1) is Schur
  intro z hz
  unfold Theta_of_J
  exact hSchur z hz

/-- The pinch Θ associated to J_pinch via the Cayley transform. -/
def Θ_pinch_of (det2 O ξ : ℂ → ℂ) : ℂ → ℂ :=
  Theta_of_J (J_pinch det2 O ξ)

/-- Schur bound for the pinch Θ on the off-zeros domain. -/
lemma Θ_pinch_Schur_offZeros {det2 O ξ : ℂ → ℂ}
    (hRe : ∀ z ∈ HalfPlane.offZeros ξ, 0 ≤ ((F_pinch det2 O ξ) z).re) :
    IsSchurOn (Θ_pinch_of det2 O ξ) (HalfPlane.offZeros ξ) := by
  unfold Θ_pinch_of
  apply Theta_Schur_of_Re_nonneg_on
  intro z hz
  -- F_pinch = 2 * J_pinch, so Re(F_pinch) = Re(2 * J_pinch)
  simp only [F_pinch] at hRe
  exact hRe z hz

/-! ## Section 10: Pinch Certificate Structure -/

/-- Pinch certificate: packages all data needed to derive RH via the pinch route.

This structure records:
- `J`: the boundary field (typically `J_pinch det2 O ξ`)
- `hRe_offZeros`: nonnegativity of `Re(2·J)` off the zeros of ξ (ensures Schur bound)
- `existsRemovable`: for each zero ρ of ξ in Ω, a removable extension exists

The Schur bound follows from `hRe_offZeros` via `Theta_Schur_of_Re_nonneg_on`. -/
structure PinchCertificate (ξ : ℂ → ℂ) where
  J : ℂ → ℂ
  hRe_offZeros : ∀ z ∈ HalfPlane.offZeros ξ, 0 ≤ ((2 : ℂ) * J z).re
  existsRemovable : ∀ ρ, ρ ∈ Ω → ξ ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | ξ z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (Theta_of_J J) (U \ {ρ}) ∧
        Set.EqOn (Theta_of_J J) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

/-- Θ attached to a pinch certificate. -/
def PinchCertificate.Θ {ξ : ℂ → ℂ} (C : PinchCertificate ξ) : ℂ → ℂ := Theta_of_J C.J

/-- Schur bound on the off-zeros domain from the certificate. -/
lemma PinchCertificate.Θ_Schur_offZeros {ξ : ℂ → ℂ} (C : PinchCertificate ξ) :
    IsSchurOn C.Θ (HalfPlane.offZeros ξ) :=
  Theta_Schur_of_Re_nonneg_on C.J (HalfPlane.offZeros ξ) C.hRe_offZeros


/-! ## Section 11: Schur Globalization Theorems -/

/-- PinchConstantOfOne: If Θ is Schur on a preconnected open S and Θ(z₀) = 1 for some z₀ ∈ S,
then Θ ≡ 1 on S.

This follows from the maximum modulus principle: |Θ| ≤ 1 everywhere, so z₀ is a maximum,
and maxima of analytic functions on connected opens are constant.

Ported from riemann-finish/RS/SchurGlobalization.lean. -/
theorem PinchConstantOfOne
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ S) (hSchur : IsSchurOn Θ S)
    (z0 : ℂ) (hz0 : z0 ∈ S) (hval : Θ z0 = 1) :
    ∀ z ∈ S, Θ z = 1 := by
  -- Use the maximum modulus principle: |Θ| ≤ 1 everywhere, |Θ(z₀)| = 1 is max
  -- On a preconnected open, this implies Θ is constant
  have hdiff : DifferentiableOn ℂ Θ S := (analyticOn_iff_differentiableOn hSopen).1 hΘ
  have hmax : IsMaxOn (norm ∘ Θ) S z0 := by
    intro z hz
    have hle : Complex.abs (Θ z) ≤ 1 := hSchur z hz
    have heq : Complex.abs (Θ z0) = 1 := by simp [hval]
    simp only [Function.comp_apply, Complex.norm_eq_abs]
    calc Complex.abs (Θ z) ≤ 1 := hle
         _ = Complex.abs (Θ z0) := heq.symm
  -- Apply maximum modulus principle: Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hSconn hSopen hdiff hz0 hmax
  intro z hz
  have heq : Θ z = Θ z0 := hconst hz
  rw [heq, hval]

/-- PinchFromExtension: If Θ is Schur on S \ {ρ}, and g is an analytic extension of Θ
across ρ with g(ρ) = 1, then both g and Θ are identically 1 on their domains.

Ported from riemann-finish/RS/SchurGlobalization.lean. -/
theorem PinchFromExtension
    (S : Set ℂ) (hSopen : IsOpen S) (hSconn : IsPreconnected S) (ρ : ℂ) (hρ : ρ ∈ S)
    (Θ : ℂ → ℂ) (hΘ : AnalyticOn ℂ Θ (S \ {ρ}))
    (hSchur : IsSchurOn Θ (S \ {ρ}))
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g S)
    (heq : Set.EqOn Θ g (S \ {ρ}))
    (hval : g ρ = 1) :
    (∀ z ∈ S, g z = 1) ∧ (∀ z ∈ (S \ {ρ}), Θ z = 1) := by
  have hSchur_g : IsSchurOn g S := by
    intro z hz
    by_cases hzρ : z = ρ
    · -- at ρ, we have g ρ = 1, hence Schur bound holds
      simp only [hzρ, hval, Complex.abs.map_one, le_refl]
    · -- away from ρ, g agrees with Θ and inherits the Schur bound
      have hz_in : z ∈ (S \ {ρ}) := ⟨hz, by simp [hzρ]⟩
      have hzg : Θ z = g z := heq hz_in
      have hΘle : Complex.abs (Θ z) ≤ 1 := hSchur z hz_in
      rw [hzg] at hΘle
      exact hΘle
  have hconst := PinchConstantOfOne S hSopen hSconn g hg hSchur_g ρ hρ hval
  have hg1 : ∀ z ∈ S, g z = 1 := hconst
  have hθ1 : ∀ z ∈ (S \ {ρ}), Θ z = 1 := by
    intro z hz
    have hzg : Θ z = g z := heq hz
    have hz1 : g z = 1 := hg1 z hz.1
    rw [hzg, hz1]
  exact ⟨hg1, hθ1⟩

/-- GlobalizeAcrossRemovable: If Θ is Schur on Ω \ Z, and at some ρ ∈ Z there is an
analytic extension g on a preconnected open U with g(ρ) = 1, then g ≡ 1 on U.

This is the Schur–Herglotz pinch used to exclude off-critical zeros.

Ported from riemann-finish/RS/SchurGlobalization.lean. -/
theorem GlobalizeAcrossRemovable
    (Z : Set ℂ) (Θ : ℂ → ℂ)
    (hSchur : IsSchurOn Θ (Ω \ Z))
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hUsub : U ⊆ Ω)
    (ρ : ℂ) (hρΩ : ρ ∈ Ω) (hρU : ρ ∈ U) (hρZ : ρ ∈ Z)
    (g : ℂ → ℂ) (hg : AnalyticOn ℂ g U)
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (hUminusSub : (U \ {ρ}) ⊆ (Ω \ Z))
    (hExt : Set.EqOn Θ g (U \ {ρ}))
    (hval : g ρ = 1) :
    ∀ z ∈ U, g z = 1 := by
  -- Restrict Schur bound to U \ {ρ}
  have hSchur_U : IsSchurOn Θ (U \ {ρ}) := by
    intro z hz
    have hz_in : z ∈ (Ω \ Z) := hUminusSub hz
    exact hSchur z hz_in
  -- Apply the removable-extension pinch on U at ρ
  have hPinch := PinchFromExtension U hUopen hUconn ρ hρU Θ hΘU hSchur_U g hg hExt hval
  exact hPinch.1

/-- No off-critical zeros from Schur bound with removable extensions.

If Θ is Schur on Ω \ Z(ξ) and, for every putative zero ρ ∈ Ω, there is an
open, preconnected U ⊆ Ω with (U ∩ Z(ξ)) = {ρ} and an analytic extension
g of Θ across ρ with g(ρ) = 1 that is not identically 1 on U, then
ξ has no zeros in Ω.

Ported from riemann-finish/RS/SchurGlobalization.lean. -/
theorem no_offcritical_zeros_from_schur_full
    (ξ : ℂ → ℂ)
    (Θ : ℂ → ℂ)
    (hSchur : IsSchurOn Θ (Ω \ {z | ξ z = 0}))
    (assign : ∀ ρ, ρ ∈ Ω → ξ ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | ξ z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ ∈ Ω, ξ ρ ≠ 0 := by
  intro ρ hρΩ hξρ
  rcases assign ρ hρΩ hξρ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩
  -- Apply globalization across Z(ξ) to get g ≡ 1 on U
  have hρZ : ρ ∈ ({z | ξ z = 0} : Set ℂ) := by simp [hξρ]
  have hUminusSub : (U \ {ρ}) ⊆ (Ω \ ({z | ξ z = 0})) := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxNe : x ≠ ρ := by intro h; exact hx.2 (by simp [h])
    have hxNotZ : x ∉ ({z | ξ z = 0} : Set ℂ) := by
      intro hxZ
      have hxInCap : x ∈ (U ∩ {z | ξ z = 0}) := ⟨hxU, hxZ⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by simp [hUZeq] at hxInCap; exact hxInCap
      have : x = ρ := by simp at hxSingleton; exact hxSingleton
      exact hxNe this
    exact ⟨hUsub hxU, hxNotZ⟩
  have hAllOne : ∀ w ∈ U, g w = 1 :=
    GlobalizeAcrossRemovable ({z | ξ z = 0}) Θ hSchur
      U hUopen hUconn hUsub ρ hρΩ hρU hρZ g hg hΘU hUminusSub hExt hval
  -- Contradiction: g must be identically 1 on U
  have : g z = 1 := hAllOne z hzU
  exact (hgzne this)

/-- No off-critical zeros from a pinch certificate.

Given a pinch certificate for ξ, conclude that ξ has no zeros in Ω.
This is the core statement; RH follows when ξ is riemannXi.

This combines:
- Θ = Theta_of_J J is Schur on Ω \ Z(ξ) (from certificate + Cayley→Schur)
- Removable extensions at each zero (from certificate)
- Schur globalization: pinned limit 1 at zeros → no off-critical zeros -/
theorem no_offcritical_zeros_from_certificate {ξ : ℂ → ℂ} (C : PinchCertificate ξ) :
    ∀ ρ ∈ Ω, ξ ρ ≠ 0 := by
  -- Step 1: offZeros ξ = Ω \ {z | ξ z = 0}
  have hOffZeros : HalfPlane.offZeros ξ = Ω \ {z | ξ z = 0} := by
    ext z
    simp only [HalfPlane.offZeros, Set.mem_setOf_eq, Set.mem_diff, Set.mem_compl_iff]
  -- Step 2: Schur bound from certificate
  have hSchur : IsSchurOn C.Θ (Ω \ {z | ξ z = 0}) := by
    rw [← hOffZeros]
    exact C.Θ_Schur_offZeros
  -- Step 3: Apply no_offcritical_zeros_from_schur_full
  exact no_offcritical_zeros_from_schur_full ξ C.Θ hSchur C.existsRemovable

/-! ## Section 12: Full Bridge Assembly -/

/-- The full Route 3 bridge:
1. Construct outer O with |O| = |det2/ξ| on boundary
2. Build pinch field F = 2 · det2/(O·ξ)
3. Prove Poisson representation for F
4. Conclude Re(F) ≥ 0 from boundary unit modulus
5. Apply Cayley → Schur bridge
6. Use Schur globalization for RH

This structure packages all the hypotheses needed for the complete bridge. -/
structure FullBridgeHypotheses where
  /-- The det2 function (analytic on Ω) -/
  det2 : ℂ → ℂ
  /-- The outer function -/
  O : ℂ → ℂ
  /-- The completed xi function -/
  ξ : ℂ → ℂ
  /-- Outer is analytic and nonvanishing on Ω -/
  hOuter : OuterHalfPlane O
  /-- Boundary modulus equality: |O| = |det2/ξ| on critical line -/
  hBME : BoundaryModulusEq O (fun s => det2 s / ξ s)
  /-- The pinch field has a Poisson representation on the off-zeros domain -/
  hPoisson : HasPoissonRepOn (F_pinch det2 O ξ) (HalfPlane.offZeros ξ)
  /-- ξ doesn't vanish almost everywhere on the boundary -/
  hξ_boundary_nz : ∀ᵐ t : ℝ, ξ (boundary t) ≠ 0

/-- From full bridge hypotheses, conclude interior positivity. -/
theorem interior_positivity_from_bridge (H : FullBridgeHypotheses) :
    ∀ z ∈ HalfPlane.offZeros H.ξ, 0 ≤ ((F_pinch H.det2 H.O H.ξ) z).re := by
  -- The boundary of F_pinch has |J| = 1 where O and ξ are nonzero
  -- This means |F.re| ≤ 2, and Re(F) can be shown nonneg via Poisson
  have hBP : BoundaryPositive (F_pinch H.det2 H.O H.ξ) := by
    -- Need: (F_pinch(boundary t)).re ≥ 0 a.e.
    -- When |J| = 1, F = 2J has |F| = 2, so |Re(F)| ≤ 2
    -- The sign comes from the Poisson representation
    sorry
  exact poissonTransportOn H.hPoisson hBP

/-! ## Section 10: Main Bridge Theorem -/

/-- No off-critical zeros from Schur bound.

If `ξ = Θ/N` on the off-zeros domain, `Θ` is Schur on Ω, and `N` is nonzero on Ω,
then ξ has no zeros in Ω (i.e., all nontrivial zeros lie on the critical line).

This is the core of the Route 3 argument. -/
theorem no_offcritical_zeros_from_schur
    (D : XiSchurDecompositionOffZeros)
    (hNnonzero : ∀ z ∈ Ω, D.N z ≠ 0) :
    ∀ z ∈ Ω, xiLagarias z ≠ 0 := by
  -- The key insight: if ξ(z) = 0 for z ∈ Ω, then Θ(z) = 0.
  -- But Θ is Schur on Ω, so |Θ| ≤ 1, and Θ cannot be the zero function on an open set
  -- unless it's identically zero (but then N would need to be zero somewhere, contradiction).
  --
  -- The actual proof requires the identity principle and careful handling of isolated zeros.
  sorry

/-- RH from the Schur bridge.

Given a Schur decomposition with N globally nonzero on Ω, conclude RH. -/
theorem RH_from_schur_bridge
    (D : XiSchurDecompositionOffZeros)
    (hNnonzero : ∀ z ∈ Ω, D.N z ≠ 0) :
    RiemannHypothesis := by
  -- RH follows from no zeros in Ω + functional equation symmetry
  sorry

end OuterSchur
end ExplicitFormula
end RiemannRecognitionGeometry
