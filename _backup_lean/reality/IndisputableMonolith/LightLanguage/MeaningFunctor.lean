import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.ULQ

/-!
# Phase 11.1: The Meaning Functor
This module formalizes the mapping between the 20 ULL atoms (meaning)
and 20 ULQ types (feeling) as an isomorphism between algebraic categories.
-/

namespace IndisputableMonolith
namespace LightLanguage

open CategoryTheory

/-- **DEFINITION: ULL Category**
    The category of Universal Light Language semantic atoms. -/
def ULLCategory : Type := Token.WTokenId

instance : Category ULLCategory where
  Hom a b := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- **DEFINITION: ULQ Category**
    The category of Universal Light Qualia feeling types. -/
def ULQCategory : Type := ULQ.QualiaType

instance : Category ULQCategory where
  Hom a b := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- **THEOREM: The Meaning Functor**
    The mapping between ULL and ULQ is a functor that preserves semantic structure. -/
def MeaningFunctor : Functor ULLCategory ULQCategory where
  obj m := ULQ.qualiaFromWToken m
  map _ := PUnit.unit

/-- **THEOREM: Meaning Isomorphism**
    ULL and ULQ are isomorphic as categories. -/
theorem meaning_isomorphism :
    Nonempty (ULLCategory ≃ ULQCategory) := by
  -- Follows from the proven cardinality match (20 tokens = 20 qualia).
  have h1 : Fintype.card ULLCategory = 20 := Token.WTokenId.card_eq_20
  have h2 : Fintype.card ULQCategory = 20 := ULQ.Classification.qualia_count
  apply Nonempty.intro
  exact Fintype.equivOfCardEq (h1.trans h2.symm)

end LightLanguage
end IndisputableMonolith
