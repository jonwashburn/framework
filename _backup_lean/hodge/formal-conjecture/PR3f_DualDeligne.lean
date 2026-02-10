/-
PR 3f: Dual Deligne filtration (Deligne (1.1.6)).
-/

import Mathlib.CategoryTheory.Filtration.Basic
import Mathlib.CategoryTheory.Filtration.Subobject
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Linarith

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

namespace Filtration
namespace DecFiltration

open Opposite

variable {X : C}

section Abelian

variable [Abelian C]

/-- The quotient object `X ⧸ S`, defined as the cokernel of `S.arrow`. -/
noncomputable def quotientObj (S : Subobject X) : C :=
  cokernel S.arrow

/-- The canonical projection `X ⟶ X ⧸ S`. -/
noncomputable def quotientπ (S : Subobject X) : X ⟶ quotientObj (C := C) (X := X) S :=
  cokernel.π S.arrow

/-- If `S₁ ≤ S₂`, there is a canonical map `X ⧸ S₁ ⟶ X ⧸ S₂` commuting with projections. -/
noncomputable def quotientMap {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    quotientObj (C := C) (X := X) S₁ ⟶ quotientObj (C := C) (X := X) S₂ :=
  cokernel.desc S₁.arrow (quotientπ (C := C) (X := X) S₂) (by
    have : S₁.arrow = (Subobject.ofLE S₁ S₂ h) ≫ S₂.arrow := by
      simpa using (Subobject.ofLE_arrow (h := h))
    -- `quotientπ S₂` kills `S₂.arrow`, hence also `S₁.arrow` which factors through it.
    calc
      S₁.arrow ≫ quotientπ (C := C) (X := X) S₂
          = (Subobject.ofLE S₁ S₂ h) ≫ S₂.arrow ≫ quotientπ (C := C) (X := X) S₂ := by
              -- Avoid `simp` loops on `Subobject.ofLE`.
              rw [this]
              simp [Category.assoc]
      _ = 0 := by
            simp [quotientπ, Category.assoc])

@[simp, reassoc]
lemma quotientπ_quotientMap {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    quotientπ (C := C) (X := X) S₁ ≫ quotientMap (C := C) (X := X) h =
      quotientπ (C := C) (X := X) S₂ := by
  simp [quotientMap, quotientπ]

/-- The quotient subobject of `Xᵒᵖ` associated to `S ≤ X`. -/
noncomputable def quotientSubobject (S : Subobject X) : Subobject (Opposite.op X) := by
  classical
  -- `quotientπ S` is a cokernel map, hence epi; thus its opposite is mono.
  haveI : Epi (quotientπ (C := C) (X := X) S) := by
    dsimp [quotientπ, quotientObj]
    -- `cokernel.π` is definitionally `coequalizer.π`, hence epi.
    infer_instance
  exact Subobject.mk ((quotientπ (C := C) (X := X) S).op)

lemma quotientSubobject_antitone :
    Antitone (quotientSubobject (C := C) (X := X) : Subobject X → Subobject (Opposite.op X)) := by
  intro S₁ S₂ h12
  classical
  -- Help typeclass search: `quotientπ` is epi, hence its opposite is mono.
  haveI : Mono (quotientπ (C := C) (X := X) S₁).op := by
    haveI : Epi (quotientπ (C := C) (X := X) S₁) := by
      dsimp [quotientπ, quotientObj]
      infer_instance
    infer_instance
  haveI : Mono (quotientπ (C := C) (X := X) S₂).op := by
    haveI : Epi (quotientπ (C := C) (X := X) S₂) := by
      dsimp [quotientπ, quotientObj]
      infer_instance
    infer_instance
  -- Unfold to a comparison between `Subobject.mk`'s.
  dsimp [quotientSubobject]
  refine Subobject.mk_le_mk_of_comm ((quotientMap (C := C) (X := X) h12).op) ?_
  -- Reduce to the corresponding statement in `C` by applying `unop`.
  apply Quiver.Hom.unop_inj
  simpa using (quotientπ_quotientMap (C := C) (X := X) h12)

/-- `quotientSubobject ⊥ = ⊤`. -/
lemma quotientSubobject_bot :
    quotientSubobject (C := C) (X := X) (⊥ : Subobject X) = ⊤ := by
  classical
  -- `⊥.arrow = 0`, hence its cokernel map is an isomorphism.
  let f : ((⊥ : Subobject X) : C) ⟶ X := (⊥ : Subobject X).arrow
  have hf : f = 0 := by
    -- `simp` knows `Subobject.bot_arrow`.
    dsimp [f]
    simp
  let i : cokernel f ≅ cokernel (0 : ((⊥ : Subobject X) : C) ⟶ X) := cokernelIsoOfEq hf
  haveI : IsIso (cokernel.π f ≫ i.hom) := by
    -- `cokernel.π f ≫ i.hom = cokernel.π 0`.
    simpa [i] using
      (show IsIso (cokernel.π (0 : ((⊥ : Subobject X) : C) ⟶ X)) from inferInstance)
  haveI : IsIso (cokernel.π f) := by
    -- Cancel the isomorphism `i.hom` on the right.
    exact IsIso.of_isIso_comp_right (cokernel.π f) i.hom
  haveI : IsIso (quotientπ (C := C) (X := X) (⊥ : Subobject X)) := by
    dsimp [quotientπ]
    simpa [f] using (inferInstance : IsIso (cokernel.π f))
  haveI : Mono ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op) := by
    infer_instance
  haveI : IsIso ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op) := by
    infer_instance
  -- `Subobject.mk` of an isomorphism is `⊤`.
  simpa [quotientSubobject] using
    (Subobject.isIso_iff_mk_eq_top ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op)).1
      (inferInstance : IsIso ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op))

/-- `quotientSubobject ⊤ = ⊥`. -/
lemma quotientSubobject_top :
    quotientSubobject (C := C) (X := X) (⊤ : Subobject X) = ⊥ := by
  classical
  haveI : Epi (quotientπ (C := C) (X := X) (⊤ : Subobject X)) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) (⊤ : Subobject X)).op) := by
    infer_instance
  -- `⊤.arrow` is an iso (hence epi), so its cokernel map is `0`.
  haveI : Epi ((⊤ : Subobject X).arrow) := by infer_instance
  have hπ : quotientπ (C := C) (X := X) (⊤ : Subobject X) = 0 := by
    dsimp [quotientπ, quotientObj]
    simpa using (cokernel.π_of_epi ((⊤ : Subobject X).arrow))
  -- `Subobject.mk f = ⊥` iff `f = 0`.
  have : Subobject.mk ((quotientπ (C := C) (X := X) (⊤ : Subobject X)).op) = (⊥ : Subobject (Opposite.op X)) := by
    apply (Subobject.mk_eq_bot_iff_zero).2
    simpa [hπ]
  simpa [quotientSubobject] using this

/-- Deligne dual filtration `Fᵛ` on `Xᵒᵖ` (Deligne (1.1.6)). -/
noncomputable def dualDeligne (F : Filtration.DecFiltration (C := C) X) :
    Filtration.DecFiltration (C := Cᵒᵖ) (Opposite.op X) := by
  classical
  refine Filtration.DecFiltration.ofAntitone (C := Cᵒᵖ) (X := Opposite.op X)
    (fun n : ℤ => quotientSubobject (C := C) (X := X) (F.step (1 - n))) ?_
  intro n m hnm
  have h1 : (1 - m) ≤ (1 - n) := by linarith
  have hF : F.step (1 - n) ≤ F.step (1 - m) :=
    step_le_step_of_le (C := C) (X := X) F h1
  exact quotientSubobject_antitone (C := C) (X := X) hF

lemma dualDeligne_step (F : Filtration.DecFiltration (C := C) X) (n : ℤ) :
    (dualDeligne (C := C) (X := X) F).step n =
      quotientSubobject (C := C) (X := X) (F.step (1 - n)) := by
  simp [dualDeligne]

/-- Finiteness is preserved by Deligne dualization (Deligne (1.1.6)). -/
lemma IsFinite.dualDeligne {F : Filtration.DecFiltration (C := C) X}
    (hF : IsFinite (C := C) (X := X) F) :
    IsFinite (C := Cᵒᵖ) (X := Opposite.op X) (dualDeligne (C := C) (X := X) F) := by
  classical
  rcases hF with ⟨a, b, ha, hb⟩
  refine ⟨(1 - b), (1 - a), ?_, ?_⟩
  · intro n hn
    have : b ≤ (1 - n) := by linarith
    have hbot : F.step (1 - n) = ⊥ := hb (1 - n) this
    simp [dualDeligne_step, hbot, quotientSubobject_bot]
  · intro n hn
    have : (1 - n) ≤ a := by linarith
    have htop : F.step (1 - n) = ⊤ := ha (1 - n) this
    simp [dualDeligne_step, htop, quotientSubobject_top]

end Abelian

end DecFiltration
end Filtration

end CategoryTheory
