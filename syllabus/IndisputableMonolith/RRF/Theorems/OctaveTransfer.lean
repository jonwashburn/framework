import IndisputableMonolith.RRF.Core.Octave

/-!
# RRF Theorems: Octave Transfer

Theorems about how properties transfer between octaves.

Key insight: If two octaves are "equivalent" (have isometric strain functions),
then their equilibrium structures are the same. This is how "the same pattern"
manifests at different scales.

## Main Results

- `equilibria_transfer`: Equivalent octaves have corresponding equilibria
- `morphism_preserves_order`: Octave morphisms preserve strain ordering
-/


namespace IndisputableMonolith
namespace RRF.Theorems

open RRF.Core

/-! ## Morphism Properties -/

variable {O₁ O₂ : Octave}

/-- Octave morphisms are monotone with respect to strain ordering. -/
theorem morphism_preserves_order (f : OctaveMorphism O₁ O₂)
    {x y : O₁.State} (hxy : O₁.strain.weaklyBetter x y) :
    O₂.strain.weaklyBetter (f.map x) (f.map y) :=
  f.preserves_order x y hxy

/-- Composition of morphisms preserves ordering. -/
theorem comp_preserves_order {O₃ : Octave}
    (g : OctaveMorphism O₂ O₃) (f : OctaveMorphism O₁ O₂)
    {x y : O₁.State} (hxy : O₁.strain.weaklyBetter x y) :
    O₃.strain.weaklyBetter ((OctaveMorphism.comp g f).map x)
                            ((OctaveMorphism.comp g f).map y) :=
  (OctaveMorphism.comp g f).preserves_order x y hxy

/-! ## Equivalence Properties -/

/-- Octave equivalences preserve equilibria exactly. -/
theorem equiv_equilibria_iff (e : OctaveEquiv O₁ O₂)
    (x : O₁.State) :
    O₁.strain.isBalanced x ↔ O₂.strain.isBalanced (e.toFun.map x) := by
  simp only [StrainFunctional.isBalanced]
  rw [e.strain_eq x]

/-- Octave equivalences preserve well-posedness. -/
theorem equiv_wellPosed (e : OctaveEquiv O₁ O₂) :
    O₁.wellPosed ↔ O₂.wellPosed := by
  constructor
  · intro ⟨x, hx⟩
    use e.toFun.map x
    rw [← equiv_equilibria_iff e x]
    exact hx
  · intro ⟨y, hy⟩
    use e.invFun.map y
    -- Use the inverse strain preservation directly
    simp only [StrainFunctional.isBalanced] at *
    rw [e.strain_eq_inv y]
    exact hy

/-! ## Transfer Lemmas for Channels -/

/-- If two octaves have equivalent channels, their quality orderings agree. -/
theorem channel_quality_transfer
    {i₁ : O₁.channels.Index} {i₂ : O₂.channels.Index}
    (f : OctaveMorphism O₁ O₂)
    (hchan : ∀ x : O₁.State,
      (O₂.channels.channel i₂).stateQuality (f.map x) =
      (O₁.channels.channel i₁).stateQuality x) :
    ∀ x y : O₁.State,
      (O₁.channels.channel i₁).stateQuality x ≤
      (O₁.channels.channel i₁).stateQuality y →
      (O₂.channels.channel i₂).stateQuality (f.map x) ≤
      (O₂.channels.channel i₂).stateQuality (f.map y) := by
  intro x y hxy
  rw [hchan x, hchan y]
  exact hxy

/-! ## The "Same Pattern, Different Scale" Principle -/

/-- Two octaves manifest the same pattern if they're equivalent. -/
def samePattern (O₁ O₂ : Octave) : Prop :=
  Nonempty (OctaveEquiv O₁ O₂)

theorem samePattern_refl (O : Octave) : samePattern O O :=
  ⟨OctaveEquiv.refl O⟩

theorem samePattern_symm {O₁ O₂ : Octave} (h : samePattern O₁ O₂) :
    samePattern O₂ O₁ :=
  let ⟨e⟩ := h
  ⟨OctaveEquiv.symm e⟩

end RRF.Theorems
end IndisputableMonolith
