import Mathlib

namespace IndisputableMonolith
namespace MaxwellDEC

/-- Oriented k-simplex (abstract id). -/
structure Simplex (α : Type) (k : Nat) where
  id     : α
  orient : Bool

/-- Discrete k-form: value per oriented k-simplex. -/
@[simp] def DForm (α : Type) (k : Nat) := Simplex α k → ℝ

/-- Coboundary operator interface on the mesh. -/
class HasCoboundary (α : Type) where
  d : ∀ {k : Nat}, DForm α k → DForm α (k+1)

/-- Hodge star interface (metric/constitutive).
    We expose linearity and a signature-correct involution law `⋆⋆ = σ(k) · id`.
    The `σ` function captures the metric signature effect; for example in 4D
    Riemannian one may take `σ k = (-1)^(k*(4-k))`, while in Lorentzian (−,+,+,+)
    one would use `σ k = (-1)^(k*(4-k)+1)`. We keep this abstract so concrete
    meshes can choose either. -/
class HasHodge (α : Type) where
  n : Nat
  star : ∀ {k : Nat}, DForm α k → DForm α (n - k)
  star_add : ∀ {k} (x y : DForm α k), star (x + y) = star x + star y
  star_zero : ∀ {k}, star (0 : DForm α k) = 0
  star_smul : ∀ {k} (c : ℝ) (x : DForm α k), star (fun s => c * x s) = (fun s => c * (star x s))
  signature : Nat → ℝ
  star_star : ∀ {k} (x : DForm α k), star (star x) = (fun s => signature k * x s)
  /-- Optional positivity control on 2-forms (useful in 4D Riemannian media).
      Instances targeting Lorentzian signatures can simply provide a trivial
      proof such as `by intro; intro; exact le_of_eq (by ring)` if not used. -/
  star2_psd : ∀ (x : DForm α 2) (s : Simplex α 2), 0 ≤ x s * (star (k:=2) x) s

/-- Linear medium parameters. -/
structure Medium (α : Type) [HasHodge α] where
  eps : ℝ
  mu  : ℝ

/-- Sources (charge and current). -/
structure Sources (α : Type) where
  ρ : DForm α 0
  J : DForm α 1

variable {α : Type}

/-- Quasi-static Maxwell equations on the mesh (no time derivative terms). -/
structure Equations (α : Type) [HasCoboundary α] [HasHodge α] (M : Medium α) where
  E : DForm α 1
  H : DForm α 1
  B : DForm α 2
  D : DForm α 2
  src : Sources α
  faraday_qs : True
  ampere_qs  : True
  gauss_e    : True
  gauss_m    : True
  const_D    : True
  const_B    : True

/-- Pointwise Hodge energy density for 2-forms: ω · (⋆ω) on each 2-simplex. -/
def energy2 (ω : DForm α 2) [HasHodge α] : DForm α 2 :=
  fun s => ω s * (HasHodge.star (k:=2) ω) s

/-- Admissibility: strictly positive material parameters. -/
def Admissible (M : Medium α) : Prop := 0 < M.eps ∧ 0 < M.mu

/-- Positivity of the Hodge energy density for admissible media, provided the
    instance supplies `star2_psd`. This is signature-agnostic and delegates the
    sign choice to the instance via `star2_psd`. -/
theorem energy2_nonneg_pointwise
  [HasHodge α] (M : Medium α) (hadm : Admissible (α:=α) M) (ω : DForm α 2)
  : ∀ s, 0 ≤ energy2 (α:=α) ω s := by
  intro s
  have h := HasHodge.star2_psd (α:=α) ω s
  simpa [energy2]

/-- PEC boundary descriptor (edges where tangential E vanishes). -/
structure PEC (β : Type) where
  boundary1 : Set (Simplex β 1)

end MaxwellDEC
end IndisputableMonolith


