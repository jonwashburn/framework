/-
Copyright (c) 2024 Hodge Project Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hodge Project Contributors
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular Homology Skeleton

This file provides abbreviations for singular homology functors from Mathlib.

## Main Definitions

* `SingularChainComplex` - Abbreviation for `singularChainComplexFunctor`
* `SingularHomology` - Abbreviation for `singularHomologyFunctor`

-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

section

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] [CategoryWithHomology C] (n : ℕ)

/-- Abbreviation for the singular chain complex functor with coefficients in `C`. -/
abbrev SingularChainComplex : C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  singularChainComplexFunctor C

/-- Abbreviation for the `n`-th singular homology functor with coefficients in `C`. -/
abbrev SingularHomology : C ⥤ TopCat.{w} ⥤ C :=
  singularHomologyFunctor C n

end