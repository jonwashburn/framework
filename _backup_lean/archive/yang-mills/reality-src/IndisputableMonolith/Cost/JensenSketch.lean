import Mathlib
import IndisputableMonolith.Cost.JcostCore

namespace IndisputableMonolith
namespace Cost

-- Use canonical definitions from JcostCore; do not redefine them locally

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 :=
  IndisputableMonolith.Cost.Jcost_exp t

-- Reuse JensenSketch from core
open IndisputableMonolith.Cost

instance (priority := 95) averagingAgree_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingAgree F :=
  ⟨by
    intro t
    have hu := JensenSketch.axis_upper (F:=F) t
    have hl := JensenSketch.axis_lower (F:=F) t
    exact le_antisymm_iff.mp ⟨hu, hl⟩⟩

/-- Concrete template to build a `JensenSketch` instance from exp-axis bounds proven via
    strict convexity/averaging on the log-axis. Provide symmetry (`SymmUnit F`) and the
    two inequalities against the cosh-based benchmark; the equalities are then discharged
    by rewriting with `Jcost_exp`. -/
noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

/-- Turn an even, strictly-convex log-domain model `G` into a cost `F := G ∘ log`,
    providing symmetry on ℝ>0 and matching exp-axis bounds against `Jcost` via cosh. -/
noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

/-- A minimal interface for log-domain models: evenness, normalization at 0,
    and two-sided cosh bounds. This is sufficient to derive T5 for `F_ofLog G`. -/
class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

/-- Symmetry and unit for `F_ofLog G` follow from the log-model axioms. -/
instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simpa using Real.log_inv hx
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        have := LogModel.even_log (G:=G) (Real.log x)
        rw [this]
      rw [hlog, he]
    , unit0 := by
      dsimp [F_ofLog]
      simpa [Real.log_one] using (LogModel.base0 (G:=G)) }

/-- From a log-model, obtain the exp-axis bounds required by Jensen and hence a `JensenSketch`. -/
instance (priority := 90) (G : ℝ → ℝ) [LogModel G] : JensenSketch (F_ofLog G) :=
  JensenSketch.of_log_bounds (F:=F_ofLog G)
    (symm := (inferInstance : SymmUnit (F_ofLog G)))
    (upper_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.upper_cosh (G:=G) t))
    (lower_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.lower_cosh (G:=G) t))

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

/-- Full uniqueness: exp‑axis agreement implies F = Jcost on ℝ_{>0}. -/
theorem F_eq_J_on_pos {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  agree_on_exp_extends (F:=F) hAgree

/-- Convenience: if averaging agreement is provided as an instance, conclude F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

/-- If an averaging derivation instance is available (encodes symmetry+unit and the convex averaging step),
    conclude exp-axis agreement. -/
theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

/-- Convenience: symmetry+unit with an averaging derivation yields F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

/-- T5 (cost uniqueness on ℝ_{>0}): if `F` satisfies the JensenSketch obligations,
    then `F` agrees with `Jcost` on positive reals. -/
theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := (averagingAgree_of_jensen (F:=F)).agrees)

/-- T5 for log-models: any `G` satisfying `LogModel` yields a cost `F := G ∘ log`
    that agrees with `Jcost` on ℝ>0. -/
theorem T5_for_log_model {G : ℝ → ℝ} [LogModel G] :
  ∀ {x : ℝ}, 0 < x → F_ofLog G x = Jcost x :=
  T5_cost_uniqueness_on_pos (F:=F_ofLog G)

-- Canonical instances for Jcost exist in JcostCore; no duplication here

end Cost
end IndisputableMonolith
