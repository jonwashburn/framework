import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
open IndisputableMonolith

/-!
# Paper-Ready T5 Exports (Lightweight Fallback)

This module provides a lightweight, paper-safe export of the T5 uniqueness
statement decoupled from heavier dependencies. It is intended as a fallback
when broader builds pull in brittle modules elsewhere in the tree.

The constructive implementation lives in the Cost modules; this file exposes
the same statement shape for citation without importing those modules. The term
"constructive" here refers to the project's goal of having `exact placeholder`-free proofs
built upon the classical real analysis framework provided by Mathlib.
-/

namespace IndisputableMonolith
namespace Verification
namespace T5ExportsLight

open Real

/-!
T5 uniqueness on ℝ₊ via the constructive functional-equation path.

Assumptions:
- Reciprocity symmetry on ℝ₊
- Unit normalization F(1)=0
- Second derivative at 0 in log-coordinates: (F∘exp)''(0)=1
- Continuity of G_F := F ∘ exp on ℝ
- Direct cosh-add identity for G_F

Conclusion: F(x) = Jcost(x) for all x > 0.
-/
theorem t5_uniqueness
  (F : ℝ → ℝ)
  (h : (∀ {x}, 0 < x → F x = F x⁻¹) ∧
    F 1 = 0 ∧
       (deriv (deriv (F ∘ Real.exp)) 0 = 1) ∧
       Continuous (fun t => F (Real.exp t)) ∧
       IndisputableMonolith.Cost.FunctionalEquation.DirectCoshAdd (fun t => F (Real.exp t))) :
  ∀ {x}, 0 < x → F x = IndisputableMonolith.Cost.Jcost x := by
  classical
  rcases h with ⟨hSymm, hUnit, hDeriv2, hContG, hDirect⟩
  -- Define G_F := F ∘ exp
  let Gf : ℝ → ℝ := fun t => F (Real.exp t)
  -- Evenness from reciprocal symmetry
  have h_even : Function.Even Gf := by
    have := IndisputableMonolith.Cost.FunctionalEquation.G_even_of_reciprocal_symmetry F (by intro x hx; simpa using (hSymm (x:=x) hx))
    simpa [IndisputableMonolith.Cost.FunctionalEquation.G, Gf] using this
  -- Zero at 0 from unit normalization
  have h_zero : Gf 0 = 0 := by
    have := IndisputableMonolith.Cost.FunctionalEquation.G_zero_of_unit F hUnit
    simpa [IndisputableMonolith.Cost.FunctionalEquation.G, Gf] using this
  -- Second derivative at 0 as given
  have h_d2 : deriv (deriv Gf) 0 = 1 := by
    simpa [IndisputableMonolith.Cost.FunctionalEquation.G, Gf] using hDeriv2
  -- Continuity of Gf
  have h_cont : Continuous Gf := by
    simpa [Gf] using hContG
  -- Direct cosh-add identity for Gf
  have h_dir : IndisputableMonolith.Cost.FunctionalEquation.DirectCoshAdd Gf := by
    simpa [IndisputableMonolith.Cost.FunctionalEquation.DirectCoshAdd, Gf] using hDirect
  -- Uniqueness: Gf(t) = cosh t - 1
  have hG : ∀ t, Gf t = Real.cosh t - 1 :=
    IndisputableMonolith.Cost.FunctionalEquation.dAlembert_uniqueness_cosh
      Gf h_even h_zero h_d2 h_cont h_dir
  -- Translate back to F(x) = Jcost(x) on ℝ₊ via t = log x
  intro x hx
  have hx' : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx
  have : F x = Real.cosh (Real.log x) - 1 := by
    have := hG (Real.log x)
    simpa [Gf, hx'] using this
  -- Jcost matches cosh-1 in log-coordinates
  have hJ : IndisputableMonolith.Cost.Jcost (Real.exp (Real.log x)) = Real.cosh (Real.log x) - 1 := by
    simpa using IndisputableMonolith.Cost.FunctionalEquation.Jcost_G_eq_cosh_sub_one (Real.log x)
  simpa [hx'] using this.trans hJ.symm

end T5ExportsLight
end Verification
end IndisputableMonolith