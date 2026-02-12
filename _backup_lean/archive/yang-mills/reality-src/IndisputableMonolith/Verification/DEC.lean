import Mathlib
import IndisputableMonolith.MaxwellDEC

namespace IndisputableMonolith

/-! ## Electromagnetism (strict bridge skeleton via DEC)
    Minimal, admit-free cochain skeleton sufficient to state Bianchi (dF=0),
    gauge invariance of F=dA, and current conservation from Ampère (d(*F)=J ⇒ dJ=0).
    This abstracts the discrete complex and avoids committing to a particular
    mesh; concrete instances provide the cochains and coboundaries. -/
namespace DEC

universe u₃

/-- Additively-written cochain space up to degree 3 with coboundaries d₀..d₃.
    The dd=0 laws are included as structure fields, so downstream lemmas are
    admit-free once an instance is provided. -/
structure CochainSpace (A : Type u) [AddCommMonoid A] where
  d0 : A → A
  d1 : A → A
  d2 : A → A
  d3 : A → A
  d0_add : ∀ x y, d0 (x + y) = d0 x + d0 y
  d1_add : ∀ x y, d1 (x + y) = d1 x + d1 y
  d2_add : ∀ x y, d2 (x + y) = d2 x + d2 y
  d3_add : ∀ x y, d3 (x + y) = d3 x + d3 y
  d0_zero : d0 0 = 0
  d1_zero : d1 0 = 0
  d2_zero : d2 0 = 0
  d3_zero : d3 0 = 0
  dd01 : ∀ x, d1 (d0 x) = 0
  dd12 : ∀ x, d2 (d1 x) = 0
  dd23 : ∀ x, d3 (d2 x) = 0

namespace CochainSpace

variable {A : Type u} [AddCommMonoid A]

/-- Field strength 2-cochain from a 1-cochain potential. -/
def F (X : CochainSpace A) (A1 : A) : A := X.d1 A1

/-- Bianchi identity (strict): dF = 0. -/
theorem bianchi (X : CochainSpace A) (A1 : A) : X.d2 (X.F A1) = 0 := by
  unfold F
  simpa using X.dd12 A1

/-- Gauge transform of the 1-cochain potential by a 0-cochain χ. -/
def gauge (X : CochainSpace A) (A1 χ : A) : A := A1 + X.d0 χ

/-- Gauge invariance: F(A + dχ) = F(A). -/
theorem F_gauge_invariant (X : CochainSpace A) (A1 χ : A) :
  X.F (X.gauge A1 χ) = X.F A1 := by
  unfold F gauge
  have h := X.d1_add A1 (X.d0 χ)
  simpa [h, X.dd01 χ]

/-- Minimal constitutive layer: a degree-preserving "Hodge" on 2-cochains.
    We keep only additive structure and expose a signature endomorphism `σ` so that
    `⋆⋆ = σ`. Concrete realizations over function spaces can choose `σ = ± id` or
    more general additive endomorphisms derived from metric signatures. -/
structure MaxwellModel (A : Type u) [AddCommMonoid A] extends CochainSpace A where
  star2 : A → A
  star2_add : ∀ x y, star2 (x + y) = star2 x + star2 y
  star2_zero : star2 0 = 0
  sigma2 : A → A
  sigma2_add : ∀ x y, sigma2 (x + y) = sigma2 x + sigma2 y
  sigma2_zero : sigma2 0 = 0
  star2_star2 : ∀ x, star2 (star2 x) = sigma2 x

namespace MaxwellModel

variable {A : Type u} [AddCommMonoid A]

/-- Ampère law (DEC form): J := d(*F). -/
def J (M : MaxwellModel A) (A1 : A) : A :=
  M.d2 (M.star2 (M.d1 A1))

/-- Continuity (strict): dJ = 0 follows from dd=0. -/
theorem current_conservation (M : MaxwellModel A) (A1 : A) :
  M.d3 (M.J A1) = 0 := by
  unfold J
  simpa using M.dd23 (M.star2 (M.d1 A1))

/-- J is additive in the potential, using additivity of d₁, ⋆, and d₂. -/
theorem J_add (M : MaxwellModel A) (A1 A2 : A) :
  M.J (A1 + A2) = M.J A1 + M.J A2 := by
  unfold J
  have h1 := M.d1_add A1 A2
  have h2 := M.star2_add (M.d1 A1) (M.d1 A2)
  have h3 := M.d2_add (M.star2 (M.d1 A1)) (M.star2 (M.d1 A2))
  simpa [h1, h2, h3]

/-- J of zero potential is zero. -/
theorem J_zero (M : MaxwellModel A) : M.J 0 = 0 := by
  unfold J
  simpa [M.d1_zero, M.star2_zero, M.d2_zero]

end MaxwellModel
end CochainSpace

end DEC

/-! ## Electromagnetism (4D covariant DEC instance, typed)
    Typed 4D cochain complex C⁰..C⁴ with d₀..d₃ and dd=0, plus a Maxwell model
    with a 2-form Hodge placeholder ⋆ : C² → C². Proves Bianchi, gauge invariance,
    and current conservation in the typed setting. -/
namespace DEC4D

universe u

structure Complex4D
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4] where
  d0 : C0 → C1
  d1 : C1 → C2
  d2 : C2 → C3
  d3 : C3 → C4
  d0_add : ∀ x y, d0 (x + y) = d0 x + d0 y
  d1_add : ∀ x y, d1 (x + y) = d1 x + d1 y
  d2_add : ∀ x y, d2 (x + y) = d2 x + d2 y
  d3_add : ∀ x y, d3 (x + y) = d3 x + d3 y
  d0_zero : d0 0 = 0
  d1_zero : d1 0 = 0
  d2_zero : d2 0 = 0
  d3_zero : d3 0 = 0
  dd01 : ∀ a, d1 (d0 a) = 0
  dd12 : ∀ a, d2 (d1 a) = 0
  dd23 : ∀ a, d3 (d2 a) = 0

namespace Complex4D

variable {C0 C1 C2 C3 C4 : Type u}
variable [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
variable [AddCommMonoid C3] [AddCommMonoid C4]

def F (X : Complex4D C0 C1 C2 C3 C4) (A : C1) : C2 := X.d1 A

theorem bianchi (X : Complex4D C0 C1 C2 C3 C4) (A : C1) :
  X.d2 (X.F A) = 0 := by
  unfold F
  simpa using X.dd12 A

def gauge (X : Complex4D C0 C1 C2 C3 C4) (A : C1) (χ : C0) : C1 := A + X.d0 χ

theorem F_gauge_invariant (X : Complex4D C0 C1 C2 C3 C4) (A : C1) (χ : C0) :
  X.F (X.gauge A χ) = X.F A := by
  unfold F gauge
  have h := X.d1_add A (X.d0 χ)
  simpa [h, X.dd01 χ]

structure MaxwellModel4D
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4]
  extends Complex4D C0 C1 C2 C3 C4 where
  star2 : C2 → C2
  star2_add : ∀ x y, star2 (x + y) = star2 x + star2 y
  star2_zero : star2 0 = 0
  sigma2 : C2 → C2
  sigma2_add : ∀ x y, sigma2 (x + y) = sigma2 x + sigma2 y
  sigma2_zero : sigma2 0 = 0
  star2_star2 : ∀ x, star2 (star2 x) = sigma2 x

namespace MaxwellModel4D

variable {C0 C1 C2 C3 C4 : Type u}
variable [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
variable [AddCommMonoid C3] [AddCommMonoid C4]

def J (M : MaxwellModel4D C0 C1 C2 C3 C4) (A : C1) : C3 :=
  M.toComplex4D.d2 (M.star2 (M.toComplex4D.d1 A))

theorem current_conservation (M : MaxwellModel4D C0 C1 C2 C3 C4) (A : C1) :
  M.toComplex4D.d3 (M.J A) = 0 := by
  unfold J
  simpa using M.toComplex4D.dd23 (M.star2 (M.toComplex4D.d1 A))

/-- J is additive in the potential, using additivity of d₁, ⋆, and d₂. -/
theorem J_add (M : MaxwellModel4D C0 C1 C2 C3 C4) (A1 A2 : C1) :
  M.J (A1 + A2) = M.J A1 + M.J A2 := by
  unfold J
  have h1 := M.toComplex4D.d1_add A1 A2
  have h2 := M.star2_add (M.toComplex4D.d1 A1) (M.toComplex4D.d1 A2)
  have h3 := M.toComplex4D.d2_add (M.star2 (M.toComplex4D.d1 A1)) (M.star2 (M.toComplex4D.d1 A2))
  simpa [h1, h2, h3]

/-- J of zero potential is zero. -/
theorem J_zero (M : MaxwellModel4D C0 C1 C2 C3 C4) : M.J 0 = 0 := by
  unfold J
  simpa [M.toComplex4D.d1_zero, M.star2_zero, M.toComplex4D.d2_zero]

end MaxwellModel4D

/-- Trivial 4D Maxwell model builder: zero coboundaries and identity ⋆. -/
def trivial
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4] :
  MaxwellModel4D C0 C1 C2 C3 C4 :=
{ d0 := fun _ => 0
, d1 := fun _ => 0
, d2 := fun _ => 0
, d3 := fun _ => 0
, d0_add := by intro x y; simp
, d1_add := by intro x y; simp
, d2_add := by intro x y; simp
, d3_add := by intro x y; simp
, d0_zero := by simp
, d1_zero := by simp
, d2_zero := by simp
, d3_zero := by simp
, dd01 := by intro a; simp
, dd12 := by intro a; simp
, dd23 := by intro a; simp
, star2 := id
, star2_add := by intro x y; rfl
, star2_zero := by rfl
, sigma2 := id
, sigma2_add := by intro x y; rfl
, sigma2_zero := by rfl
, star2_star2 := by intro x; rfl }

/-! ### Bridge: mesh-level Hodge to typed 4D model on 2-cochains
    When the mesh `HasHodge` is 4D (`n=4`) and the degree-2 cochains are
    represented as functions on 2-simplices, we can wire the Hodge ⋆ into the
    typed model so that `⋆⋆ = σ` with `σ` given pointwise by the signature map. -/
namespace Bridge

open IndisputableMonolith.MaxwellDEC

variable {α : Type}

/-- Specialize mesh Hodge to a 2-form star in 4D. -/
def meshStar2 [HasHodge α] (h4 : HasHodge.n = 4) : DForm α 2 → DForm α 2 :=
  fun ω => by
    cases h4
    simpa using (HasHodge.star (α:=α) (k:=2) ω)

/-- Signature endomorphism on 2-forms induced by the mesh signature. -/
def meshSigma2 [HasHodge α] : DForm α 2 → DForm α 2 :=
  fun ω s => HasHodge.signature (α:=α) 2 * ω s

/-- Additivity of the mesh-induced σ on 2-forms. -/
theorem meshSigma2_add [HasHodge α] :
  ∀ x y : DForm α 2, meshSigma2 (α:=α) (fun s => x s + y s) =
    (fun s => meshSigma2 (α:=α) x s + meshSigma2 (α:=α) y s) := by
  intro x y; funext s; simp [meshSigma2, mul_add]

/-- Zero law for the mesh-induced σ on 2-forms. -/
theorem meshSigma2_zero [HasHodge α] : meshSigma2 (α:=α) (0 : DForm α 2) = 0 := by
  funext s; simp [meshSigma2]

/-- Additivity of the mesh ⋆ on 2-forms (from the class law). -/
theorem meshStar2_add [HasHodge α] (h4 : HasHodge.n = 4) :
  ∀ x y : DForm α 2, meshStar2 (α:=α) h4 (fun s => x s + y s) =
    (fun s => meshStar2 (α:=α) h4 x s + meshStar2 (α:=α) h4 y s) := by
  intro x y
  cases h4
  funext s
  simpa using (HasHodge.star_add (α:=α) (k:=2) x y) 

/-- Zero law of the mesh ⋆ on 2-forms. -/
theorem meshStar2_zero [HasHodge α] (h4 : HasHodge.n = 4) :
  meshStar2 (α:=α) h4 (0 : DForm α 2) = 0 := by
  cases h4
  funext s
  simpa using (HasHodge.star_zero (α:=α) (k:=2))

/-- Involution law of the mesh ⋆ on 2-forms with signature σ. -/
theorem mesh_star2_star2 [HasHodge α] (h4 : HasHodge.n = 4) :
  ∀ ω, meshStar2 (α:=α) h4 (meshStar2 (α:=α) h4 ω) = meshSigma2 (α:=α) ω := by
  intro ω
  cases h4
  funext s
  simpa [meshSigma2] using (HasHodge.star_star (α:=α) (k:=2) ω) 

end Bridge

/-! ### Negative controls (constitutive map counterexamples)
    These show that if one were to pick a non-additive ⋆ on 2-cochains, the
    constitutive laws would fail (linearity and involution), even though Bianchi
    (dd=0) and continuity (d∘d=0) are purely complex-theoretic and remain valid. -/
namespace Counterexample

/-- A deliberately non-additive map on an additive monoid: x ↦ x + 1 on ℤ. -/
def badStar2 (x : ℤ) : ℤ := x + 1

/-- `badStar2` breaks additivity: `⋆(x+y) ≠ ⋆x + ⋆y` (e.g. at 0,0). -/
lemma badStar2_not_add : ∃ x y : ℤ, badStar2 (x + y) ≠ badStar2 x + badStar2 y := by
  refine ⟨0, 0, ?_⟩
  simp [badStar2]

/-- `badStar2` also breaks involution `⋆⋆ = id` (e.g. at 0). -/
lemma badStar2_not_involution : badStar2 (badStar2 0) ≠ 0 := by
  simp [badStar2]

/-- There is no CochainSpace.MaxwellModel on ℤ whose ⋆ equals `badStar2`. -/
lemma no_MaxwellModel_with_badStar2 :
  ¬ ∃ (M : DEC.CochainSpace.MaxwellModel ℤ), M.star2 = badStar2 := by
  intro h
  rcases h with ⟨M, hM⟩
  have hadd := M.star2_add (0 : ℤ) 0
  -- Expand both sides using `hM` and derive 1 ≠ 2
  have := congrArg (fun f => f) hadd
  -- Evaluate both sides at integers; this is a plain equality in ℤ
  -- Left: badStar2 (0+0) = 1; Right: badStar2 0 + badStar2 0 = 2
  have : badStar2 (0 + 0) = badStar2 0 + badStar2 0 := by simpa [hM]
  simp [badStar2] at this

/-- There is no 4D typed Maxwell model on ℤ-cochains whose ⋆ equals `badStar2`. -/
lemma no_MaxwellModel4D_with_badStar2 :
  ¬ ∃ (M : DEC4D.MaxwellModel4D ℤ ℤ ℤ ℤ ℤ), M.star2 = badStar2 := by
  intro h
  rcases h with ⟨M, hM⟩
  have hadd := M.star2_add (0 : ℤ) 0
  have : badStar2 (0 + 0) = badStar2 0 + badStar2 0 := by simpa [hM]
  simp [badStar2] at this

end Counterexample

end Complex4D
end DEC4D

/-! ### Compatibility re-exports (MaxwellDEC alias)
Omitted in WIP to avoid instance inference issues. Use DEC.* and DEC4D.* directly.
-/
namespace MaxwellDEC
end MaxwellDEC

end IndisputableMonolith
