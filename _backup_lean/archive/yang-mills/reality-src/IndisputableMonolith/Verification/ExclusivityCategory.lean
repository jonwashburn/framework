import Mathlib
import Mathlib.CategoryTheory.Equivalence
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.URCAdapters.Reports

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace Cat

open CategoryTheory
open IndisputableMonolith
open IndisputableMonolith.RH.RS

universe u

/-! # Frameworks at φ as a category and equivalence to a canonical skeleton

Objects are `ZeroParamFramework φ`.
Morphisms are equivalences between their units quotients that send the
canonical units class to the canonical units class. By one‑pointness of
these quotients, such a morphism is unique when it exists, and is always
provided by `unitsQuot_equiv`.

We build a one‑object canonical category and show an equivalence.
This reuses the existing units‑quotient infrastructure and canonical class
lemmas from `Spec.lean` and the uniqueness context from `Exclusivity.lean`.
-/

variable {φ : ℝ}

abbrev FrameworksAt (φ : ℝ) := ZeroParamFramework φ

/-- Morphisms are equivalences of units quotients preserving canonical class. -/
def Mor (φ : ℝ) (F G : FrameworksAt φ) : Type :=
  { e : UnitsQuotCarrier F ≃ UnitsQuotCarrier G //
      e (canonicalUnitsClass φ F) = canonicalUnitsClass φ G }

namespace Mor

variable (φ) {F G H : FrameworksAt φ}

@[simp]
def id (F : FrameworksAt φ) : Mor φ F F :=
  ⟨Equiv.refl _, by simp⟩

@[simp]
def comp (f : Mor φ F G) (g : Mor φ G H) : Mor φ F H := by
  refine ⟨f.1.trans g.1, ?_⟩
  have hf := f.2
  have hg := g.2
  -- Transport canonical class along f then g
  have : g.1 (f.1 (canonicalUnitsClass φ F)) = canonicalUnitsClass φ H := by
    simpa [hf]
      using hg
  simpa [Equiv.trans] using this

@[simp]
lemma comp_e (f : Mor φ F G) (g : Mor φ G H) :
    (comp (φ:=φ) f g).1 = f.1.trans g.1 := rfl

@[simp]
lemma id_e (F : FrameworksAt φ) : (id (φ:=φ) F).1 = Equiv.refl _ := rfl

@[simp]
lemma comp_id (f : Mor φ F G) : comp (φ:=φ) (id (φ:=φ) F) f = f := by
  -- ext on the underlying equivalence; the property component follows by proof-irrelevance
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp [comp, id]

@[simp]
lemma id_comp (f : Mor φ F G) : comp (φ:=φ) f (id (φ:=φ) G) = f := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp [comp, id]

@[simp]
lemma assoc (f : Mor φ F G) (g : Mor φ G H) {I : FrameworksAt φ} (h : Mor φ H I) :
    comp (φ:=φ) (comp (φ:=φ) f g) h = comp (φ:=φ) f (comp (φ:=φ) g h) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simp [comp, Function.comp, Equiv.trans]

end Mor

instance instFrameworksAtCategory (φ : ℝ) : Category (FrameworksAt φ) where
  Hom F G := Mor φ F G
  id F := Mor.id (φ:=φ) F
  comp f g := Mor.comp (φ:=φ) f g
  id_comp := by intro F G f; simpa using Mor.id_comp (φ:=φ) f
  comp_id := by intro F G f; simpa using Mor.comp_id (φ:=φ) f
  assoc := by intro F G H I f g h; simpa using Mor.assoc (φ:=φ) f g (h:=h)

/‑! ## Canonical one‑object target category -/

abbrev Canonical (φ : ℝ) := PUnit

instance instCanonicalCategory (φ : ℝ) : Category (Canonical φ) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/‑! ## Canonical representative framework and canonical morphisms -/

noncomputable def canonicalFramework (φ : ℝ) : FrameworksAt φ :=
  IndisputableMonolith.URCAdapters.Reports.routeAZeroParamFramework φ

noncomputable def toMorCanonical (F G : FrameworksAt φ) : Mor φ F G :=
  ⟨ unitsQuot_equiv F G
  , by simpa using unitsQuot_equiv_maps_canonical (φ:=φ) F G ⟩

/‑! ## Functors F : FrameworksAt φ ⥤ Canonical φ and G : Canonical φ ⥤ FrameworksAt φ -/

noncomputable def F_functor (φ : ℝ) : (FrameworksAt φ) ⥤ (Canonical φ) where
  obj := fun _ => PUnit.unit
  map := fun _ _ _ => ⟨⟩

noncomputable def G_functor (φ : ℝ) : (Canonical φ) ⥤ (FrameworksAt φ) where
  obj := fun _ => canonicalFramework φ
  map := fun _ _ _ => Mor.id (φ:=φ) (canonicalFramework φ)

/‑! ## Equivalence data -/

noncomputable def unitIso (φ : ℝ) :
    𝟭 (FrameworksAt φ) ≅ (F_functor φ) ⋙ (G_functor φ) := by
  -- Component at F: F ⟶ canonicalFramework φ via the canonical units‑quot equivalence
  refine
    { hom := { app := fun F => toMorCanonical (φ:=φ) F (canonicalFramework φ) }
    , inv := { app := fun F => toMorCanonical (φ:=φ) (canonicalFramework φ) F }
    , hom_inv_id := ?hid
    , inv_hom_id := ?ihid };
  · -- hom ≫ inv = 𝟙
    funext F
    apply Subtype.ext
    apply Equiv.ext
    intro x
    -- use coherence of unitsQuot_equiv
    simp [toMorCanonical, Equiv.trans, unitsQuot_equiv_trans, unitsQuot_equiv_refl]
  · -- inv ≫ hom = 𝟙
    funext F
    apply Subtype.ext
    apply Equiv.ext
    intro x
    simp [toMorCanonical, Equiv.trans, unitsQuot_equiv_trans, unitsQuot_equiv_refl]

noncomputable def counitIso (φ : ℝ) :
    (G_functor φ) ⋙ (F_functor φ) ≅ 𝟭 (Canonical φ) := by
  -- Everything is constant at the sole object; identity everywhere
  refine
    { hom := { app := fun _ => ⟨⟩ }
    , inv := { app := fun _ => ⟨⟩ }
    , hom_inv_id := by funext x; rfl
    , inv_hom_id := by funext x; rfl }

/-- The main equivalence. -/
noncomputable def frameworks_equiv_canonical (φ : ℝ) :
    (FrameworksAt φ) ≌ (Canonical φ) :=
  { functor := F_functor φ
  , inverse := G_functor φ
  , unitIso := unitIso φ
  , counitIso := counitIso φ }

/-- A stable alias that highlights the role of `DefinitionalUniqueness φ`.
     The equivalence is constructed using the canonical `unitsQuot_equiv` and
     does not require additional axioms, but `DefinitionalUniqueness φ` ensures
     that the unit components align with the definitional witnesses. -/
theorem frameworks_equiv_canonical_of_defUniq
  (φ : ℝ) (hDU : DefinitionalUniqueness φ) :
  (FrameworksAt φ) ≌ (Canonical φ) :=
  frameworks_equiv_canonical φ

end Cat
end Exclusivity
end Verification
end IndisputableMonolith
