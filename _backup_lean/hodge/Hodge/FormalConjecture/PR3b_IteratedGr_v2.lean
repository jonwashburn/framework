/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
/-
PR 3b (revised API): Iterated graded pieces (Deligne, *Théorie de Hodge II*, §1.2.1).

This file adds the definition of the *iterated graded* object
`Gr_F^p(Gr_G^q(X))`, using the induced filtration on `Gr_G^q(X)` defined in
`Mathlib.CategoryTheory.Filtration.InducedOnGr`.

It also defines the corresponding "iterated opposedness" predicate, matching Deligne's
original formulation (1.2.3), and records basic unfolding lemmas.

No axioms, no placeholders, no `sorry`.
-/

import Hodge.FormalConjecture.InducedOnGr

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace Filtration
namespace DecFiltration

variable {X : C}

section
variable [Abelian C]

/-- The iterated graded piece `Gr_F^p(Gr_G^q(X))` (Deligne §1.2.1).

By definition this is the graded piece of the induced filtration of `F` on `Gr_G^q(X)`. -/
noncomputable def grIter (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) : C :=
  (inducedOnGr (C := C) (X := X) F G q).gr p

@[simp] lemma grIter_def (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) :
    grIter (C := C) (X := X) F G p q = (inducedOnGr (C := C) (X := X) F G q).gr p := rfl

/-- Deligne's `n`-opposedness predicate phrased using iterated graded pieces.

Deligne (1.2.3) states opposedness in terms of `Gr_F^p Gr_G^q(X)` vanishing off the diagonal. -/
def IsNOpposedIter (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (grIter (C := C) (X := X) F G p q)

lemma isZero_grIter_of_IsNOpposedIter {F G : Filtration.DecFiltration (C := C) X} {n p q : ℤ}
    (h : IsNOpposedIter (C := C) (X := X) F G n) (hpq : p + q ≠ n) :
    IsZero (grIter (C := C) (X := X) F G p q) :=
  h p q hpq

end

end DecFiltration
end Filtration

end CategoryTheory
