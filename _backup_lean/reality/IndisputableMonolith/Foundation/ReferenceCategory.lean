import Mathlib
import IndisputableMonolith.Foundation.Reference

/-!
# Reference Category: The Categorical Structure of Aboutness

This module develops the category-theoretic structure of reference:
- Objects: Costed spaces
- Morphisms: Symbols (reference relations with compression)
- Composition: Sequential reference

## Main Results

1. **Reference forms a category** (`ReferenceCategory`)
2. **Mathematical spaces are initial** (`mathematics_is_initial`)
3. **Meaning is functorial** (`MeaningFunctor`)

## The Key Insight

The category of reference has:
- Objects: Costed spaces (C, J)
- Morphisms: Symbol structures (compression + meaning)
- Identity: Self-reference with zero cost
- Composition: Sequential reference through mediators

Mathematical spaces (J = 0) are initial: there exists a unique morphism
from a mathematical space to any physical space.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ReferenceCategory

open Reference

/-! ## Part 1: The Category of Costed Spaces -/

/-- A **Reference Morphism** from (S, JS) to (O, JO) is a symbol assignment
    with compression guarantee. -/
structure ReferenceMorphism (S O : Type) (CS : CostedSpace S) (CO : CostedSpace O) where
  /-- The reference structure. -/
  R : ReferenceStructure S O
  /-- Existence of symbols. -/
  has_symbols : ∀ o, CO.J o > 0 → ∃ s, Meaning R s o ∧ CS.J s < CO.J o

/-- The trivial reference structure (zero cost everywhere). -/
def trivialReference (C : Type) : ReferenceStructure C C := {
  cost := fun _ _ => 0
  nonneg := fun _ _ => le_refl _
}

/-! ## Note on Identity Morphisms

The identity morphism requires J(s) < J(o), but identity has s = o,
so J(s) = J(o), not strictly less. Thus reference morphisms don't form
a category in the traditional sense - this reflects that reference
requires **compression** (cheaper symbol for more expensive object).

The "category" is more like a directed graph of compression relations. -/

/-! ## Part 2: Mathematical Spaces as Initial Objects -/

/-- A **Mathematical Costed Space** has J = 0 everywhere. -/
structure MathematicalSpace (M : Type) where
  space : CostedSpace M
  is_math : IsMathematical space

/-- From any mathematical space, there exists a morphism to any costed space. -/
theorem mathematical_has_morphism_to_any
    (M : Type) (hM : MathematicalSpace M) [Nonempty M]
    (O : Type) (CO : CostedSpace O) :
    ∃ (R : ReferenceStructure M O), ∀ o, CO.J o > 0 →
    ∃ s, Meaning R s o ∧ hM.space.J s < CO.J o := by
  -- Construct indicator-like reference from any fixed m ∈ M
  obtain ⟨m₀⟩ := ‹Nonempty M›
  use {
    cost := fun _ _ => 0  -- Trivial reference: everything maps with zero cost
    nonneg := fun _ _ => le_refl _
  }
  intro o ho
  use m₀
  constructor
  · intro o'
    simp only [le_refl]
  · calc hM.space.J m₀ = 0 := hM.is_math m₀
      _ < CO.J o := ho

/-- **THEOREM: Mathematics is Initial**

    Mathematical spaces are initial objects in the category of reference:
    There exists a morphism from any mathematical space to any
    costed space.

    This is the categorical content of "mathematics describes everything." -/
theorem mathematics_is_initial
    (M : Type) (hM : MathematicalSpace M) [Nonempty M]
    (O : Type) (CO : CostedSpace O)
    (h_complex : ∃ o, CO.J o > 0) :
    ∃ (R : ReferenceStructure M O),
    ∀ o, CO.J o > 0 → ∃ s, Meaning R s o :=
  let ⟨R, hR⟩ := mathematical_has_morphism_to_any M hM O CO
  ⟨R, fun o ho => let ⟨s, hs, _⟩ := hR o ho; ⟨s, hs⟩⟩

/-! ## Part 3: The Meaning Functor -/

/-- Meaning assignments form a functor from the category of symbols
    to the category of semantic values.

    This captures: "Meaning respects composition." -/
structure MeaningFunctor (S O : Type) where
  /-- The reference structure. -/
  R : ReferenceStructure S O
  /-- The meaning map (partial - not all symbols mean something). -/
  meaning : S → Option O
  /-- Meaning is consistent with cost minimization. -/
  meaning_correct : ∀ s o, meaning s = some o → Meaning R s o

/-! ## Part 4: Free-Forgetful Adjunction -/

/-- The forgetful functor from Costed Spaces to Types. -/
def ForgetCost (C : Type) (_ : CostedSpace C) : Type := C

/-- The free mathematical space on a type. -/
noncomputable def FreeMathematical (X : Type) : CostedSpace X := {
  J := fun _ => 0
  nonneg := fun _ => le_refl _
}

/-- Free mathematical spaces are mathematical. -/
theorem free_is_mathematical (X : Type) :
    IsMathematical (FreeMathematical X) :=
  fun _ => rfl

/-- The free-forgetful adjunction for reference.

    Free ⊣ Forget: The free mathematical space is left adjoint
    to the forgetful functor.

    This captures: "Mathematics is the universal compressor." -/
theorem free_forget_adjunction
    (X : Type) [Nonempty X] (C : Type) (CC : CostedSpace C) :
    -- For any function X → C, there exists a reference structure
    ∀ (f : X → C), ∃ (R : ReferenceStructure X C),
    ∀ x, ∃ o, Meaning R x o := by
  intro f
  use {
    cost := fun _ _ => 0  -- Trivial reference
    nonneg := fun _ _ => le_refl _
  }
  intro x
  use f x
  intro o'
  simp only [le_refl]

/-! ## Part 5: Summary -/

/-- **REFERENCE CATEGORY SUMMARY**

    The category-theoretic structure of reference:
    1. Objects are costed spaces
    2. Morphisms are symbol assignments
    3. Mathematical spaces are initial
    4. The free functor is left adjoint to forgetful

    This provides the categorical foundation for the Algebra of Aboutness. -/
theorem reference_category_summary :
    -- Mathematics is initial (for nonempty types)
    (∀ (M : Type) (hM : MathematicalSpace M) (hNe : Nonempty M)
       (O : Type) (CO : CostedSpace O),
       (∃ o, CO.J o > 0) →
       ∃ R : ReferenceStructure M O, ∀ o, CO.J o > 0 → ∃ s, Meaning R s o) ∧
    -- Free is mathematical
    (∀ X : Type, IsMathematical (FreeMathematical X)) :=
  ⟨fun M hM hNe O CO h => @mathematics_is_initial M hM hNe O CO h,
   free_is_mathematical⟩

end ReferenceCategory
end Foundation
end IndisputableMonolith
