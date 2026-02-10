/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.CategoryTheory.Filtration.Subobject
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Opposed filtrations (Deligne)

This file defines the Zassenhaus quotient `gr₂` and the `n`-opposedness predicate in the sense of
Deligne (*Théorie de Hodge II*, §1.2.3), phrased via vanishing of `gr₂` off the diagonal.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory
namespace Filtration
namespace DecFiltration

universe v u

variable {C : Type u} [Category.{v} C]
variable {X : C}

section

variable [Abelian C]

/-- The Zassenhaus quotient `gr₂ F G p q`:
`(F^p ∩ G^q) / ((F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1}))`. -/
noncomputable def gr₂ (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) : C :=
  let Xpq : Subobject X := F.step p ⊓ G.step q
  let Ypq : Subobject X := (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1))
  have hY : Ypq ≤ Xpq := by
    classical
    refine sup_le ?_ ?_
    · have hp : p ≤ p + 1 :=
        le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide)
      have hF : F.step (p + 1) ≤ F.step p :=
        step_le_step_of_le (C := C) (X := X) F hp
      exact inf_le_inf hF le_rfl
    · have hq : q ≤ q + 1 :=
        le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide)
      have hG : G.step (q + 1) ≤ G.step q :=
        step_le_step_of_le (C := C) (X := X) G hq
      exact inf_le_inf le_rfl hG
  cokernel (Subobject.ofLE Ypq Xpq hY)

/-- Two decreasing ℤ-filtrations `F` and `G` are `n`-opposed (Deligne 1.2.3) if
`gr₂ F G p q` vanishes whenever `p + q ≠ n`. -/
def IsNOpposedGr₂ (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (gr₂ (C := C) (X := X) F G p q)

lemma isZero_gr₂_of_IsNOpposedGr₂ {F G : Filtration.DecFiltration (C := C) X} {n p q : ℤ}
    (h : IsNOpposedGr₂ (C := C) (X := X) F G n) (hpq : p + q ≠ n) :
    IsZero (gr₂ (C := C) (X := X) F G p q) :=
  h p q hpq

end

end DecFiltration
end Filtration
end CategoryTheory
