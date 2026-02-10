import IndisputableMonolith.RRF.Core.DisplayChannel
import IndisputableMonolith.RRF.Core.Strain
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# RRF Core: Octave

An octave is a scale of manifestation. The same underlying pattern can appear
at different octaves, related by scaling (φⁿ in the full theory).

Key insight:
- Particles, proteins, thoughts are "the same thing" at different octaves
- Each octave has its own display channels
- The φ-scaling is a hypothesis, not a definition (see Hypotheses/PhiLadder.lean)

This module provides the abstract octave structure without physical constants.
-/


namespace IndisputableMonolith
namespace RRF.Core

/-- An octave: a state space with strain and observation channels.

This is the abstract structure; no physical constants (φ, 8-tick) here.
Those are hypotheses layered on top.
-/
structure Octave where
  /-- The state space at this octave. -/
  State : Type*
  /-- The strain functional (J-cost). -/
  strain : StrainFunctional State
  /-- Display channels available at this octave. -/
  channels : ChannelBundle State
  /-- Non-emptiness: at least one state exists. -/
  inhabited : Nonempty State

namespace Octave

variable (O : Octave)

/-- The equilibrium states of an octave. -/
def equilibria : Set O.State := O.strain.equilibria

/-- An octave is well-posed if it has at least one equilibrium. -/
def wellPosed : Prop := ∃ x : O.State, O.strain.isBalanced x

end Octave

/-- A morphism between octaves: a map that preserves strain ordering. -/
structure OctaveMorphism (O₁ O₂ : Octave) where
  /-- The underlying map on states. -/
  map : O₁.State → O₂.State
  /-- The map preserves strain ordering. -/
  preserves_order : ∀ x y, O₁.strain.weaklyBetter x y →
                           O₂.strain.weaklyBetter (map x) (map y)

namespace OctaveMorphism

/-- Identity morphism. -/
def id (O : Octave) : OctaveMorphism O O where
  map := fun x => x
  preserves_order := fun _ _ h => h

/-- Composition of morphisms. -/
def comp {O₁ O₂ O₃ : Octave}
    (g : OctaveMorphism O₂ O₃) (f : OctaveMorphism O₁ O₂) : OctaveMorphism O₁ O₃ where
  map := g.map ∘ f.map
  preserves_order := fun x y h => g.preserves_order _ _ (f.preserves_order x y h)

/-- Morphisms preserve equilibria (if target has NonNeg strain). -/
theorem preserves_equilibria {O₁ O₂ : Octave}
    [inst : StrainFunctional.NonNeg O₂.strain]
    (f : OctaveMorphism O₁ O₂)
    (x : O₁.State) (hx : O₁.strain.isBalanced x)
    (hf : O₂.strain.J (f.map x) ≤ O₁.strain.J x) :
    O₂.strain.isBalanced (f.map x) := by
  simp only [StrainFunctional.isBalanced] at *
  rw [hx] at hf
  have h₁ := @StrainFunctional.NonNeg.nonneg _ O₂.strain inst (f.map x)
  linarith

end OctaveMorphism

/-- Two octaves are equivalent if there exist mutually inverse morphisms
    that both preserve strain exactly (isometric in both directions). -/
structure OctaveEquiv (O₁ O₂ : Octave) where
  /-- Forward morphism. -/
  toFun : OctaveMorphism O₁ O₂
  /-- Backward morphism. -/
  invFun : OctaveMorphism O₂ O₁
  /-- Strain is preserved exactly (forward isometry). -/
  strain_eq : ∀ x, O₂.strain.J (toFun.map x) = O₁.strain.J x
  /-- Strain is preserved exactly (inverse isometry). -/
  strain_eq_inv : ∀ y, O₁.strain.J (invFun.map y) = O₂.strain.J y

namespace OctaveEquiv

/-- Reflexivity. -/
def refl (O : Octave) : OctaveEquiv O O where
  toFun := OctaveMorphism.id O
  invFun := OctaveMorphism.id O
  strain_eq := fun _ => rfl
  strain_eq_inv := fun _ => rfl

/-- Symmetry. -/
def symm {O₁ O₂ : Octave} (e : OctaveEquiv O₁ O₂) : OctaveEquiv O₂ O₁ where
  toFun := e.invFun
  invFun := e.toFun
  strain_eq := e.strain_eq_inv
  strain_eq_inv := e.strain_eq

end OctaveEquiv

/-- The "octave index" in Z (integer rung number).
    This is just a type alias; the physical interpretation is in Hypotheses. -/
abbrev OctaveRung := ℤ

/-- A family of octaves indexed by rung. -/
structure OctaveFamily where
  /-- The octave at each rung. -/
  octaveAt : OctaveRung → Octave

end RRF.Core
end IndisputableMonolith
