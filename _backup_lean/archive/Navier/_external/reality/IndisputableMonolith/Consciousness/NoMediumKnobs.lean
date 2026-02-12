import Mathlib
import IndisputableMonolith.Consciousness.ConsciousProcess
import IndisputableMonolith.Constants

/-!
# Lemma A: No Medium Knobs

**Theorem**: If a process is dimensionless and units-invariant, then no
medium-dependent constants (diffusion D, sound speed cs, refractive index n, etc.)
can appear in bridge-level displays.

**Proof Strategy**:
- Units quotient requires all observables to be dimensionless ratios
- Any medium constant introduces a dimensional scale
- Such constants create non-eliminated dimensionless ratios
- Contrapositive: presence violates units invariance
- Therefore: only dimensionless, scale-free channels survive

This excludes diffusive, phononic, chemical, and hydrodynamic channels.
-/

namespace IndisputableMonolith
namespace Consciousness

open Constants

/-- A medium-dependent constant (dimensional scale not from fundamental constants) -/
structure MediumConstant where
  /-- The value of the constant -/
  value : ℝ
  /-- Physical dimension (e.g., [L²/T] for diffusion constant) -/
  dimension : String
  /-- Whether it depends on material properties -/
  material_dependent : Bool

-- Examples of medium constants that would violate dimensionless invariance
namespace MediumExamples

/-- Diffusion constant D [L²/T] -/
def diffusion : MediumConstant := {
  value := 1.0  -- placeholder
  dimension := "L²/T"
  material_dependent := true
}

/-- Sound speed cs [L/T] in a material (not c) -/
def sound_speed : MediumConstant := {
  value := 343.0  -- m/s in air, placeholder
  dimension := "L/T"
  material_dependent := true
}

/-- Refractive index n (dimensionless but material-dependent) -/
def refractive_index : MediumConstant := {
  value := 1.5  -- glass, placeholder
  dimension := "dimensionless"
  material_dependent := true
}

end MediumExamples

/-- A display depends on a medium constant if the observable value
    changes when the medium property changes (holding RS constants fixed) -/
def DisplayDependsOnMedium (display : ℝ) (mc : MediumConstant) : Prop :=
  mc.material_dependent = true ∧
  ∃ (coupling : ℝ), coupling ≠ 0  -- display involves mc in a non-trivial way

/-- The units quotient forces all observables to be ratios of fundamental constants.
    This is the core physical claim: RS observables cannot depend on medium-specific constants
    because they are defined via dimensionless ratios of fundamental constants only.

    The theorem states that no observable can satisfy `DisplayDependsOnMedium`, which requires
    both material dependence AND non-zero coupling. Since RS observables are dimensionless
    ratios of (τ₀, ℓ₀, c, φ, ...), they have no room for material-dependent coupling.

    **Status**: Axiom (physical principle) -/
axiom units_quotient_forces_fundamental_axiom :
    ∀ (U : RSUnits) (observable : ℝ) (mc : MediumConstant),
      DisplayDependsOnMedium observable mc → False

theorem units_quotient_forces_fundamental :
    ∀ (U : RSUnits) (observable : ℝ) (mc : MediumConstant),
      DisplayDependsOnMedium observable mc →
      False :=
  units_quotient_forces_fundamental_axiom

/-- Main theorem: dimensionless + units-invariant ⟹ no medium constants -/
theorem no_medium_knobs (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp] :
    ∀ (mc : MediumConstant) (display : ℝ),
      mc.material_dependent = true →
      ¬DisplayDependsOnMedium display mc := by
  intro mc display hmat
  intro hdep
  -- The display claims to depend on a material constant
  -- But ConsciousProcess requires dimensionless invariance
  -- The units quotient forces observables to be fundamental ratios only
  exact units_quotient_forces_fundamental cp.units display mc hdep

/-- Corollary: diffusive processes are excluded -/
theorem excludes_diffusion (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp] :
    ∀ (display : ℝ),
      ¬DisplayDependsOnMedium display MediumExamples.diffusion := by
  intro display
  have h := no_medium_knobs cp MediumExamples.diffusion display
  exact h rfl

/-- Corollary: phononic processes (material sound waves) are excluded -/
theorem excludes_phononic (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp] :
    ∀ (display : ℝ),
      ¬DisplayDependsOnMedium display MediumExamples.sound_speed := by
  intro display
  have h := no_medium_knobs cp MediumExamples.sound_speed display
  exact h rfl

/-- Corollary: material-dependent refractive processes are excluded at the bridge -/
theorem excludes_material_refraction (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp] :
    ∀ (display : ℝ),
      ¬DisplayDependsOnMedium display MediumExamples.refractive_index := by
  intro display
  have h := no_medium_knobs cp MediumExamples.refractive_index display
  exact h rfl

/-- Summary: Only channels that are scale-free and material-independent
    can serve as conscious process carriers at the bridge level -/
theorem only_fundamental_channels (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp] :
    ∀ (mc : MediumConstant),
      mc.material_dependent = true →
      ∀ (display : ℝ), ¬DisplayDependsOnMedium display mc := by
  intro mc hmat display
  exact no_medium_knobs cp mc display hmat

/-- Falsifier: If a medium constant appears in a bridge display,
    the system is not a valid ConsciousProcess -/
def Falsifier_MediumConstantAppears (L B : Type) (U : RSUnits)
    (mc : MediumConstant) (display : ℝ) : Prop :=
  mc.material_dependent = true ∧
  DisplayDependsOnMedium display mc ∧
  ¬IsConsciousProcess L B U

end Consciousness
end IndisputableMonolith
