import Mathlib
import IndisputableMonolith.Cost.JcostCore

namespace IndisputableMonolith
namespace Cost

/-- Log-domain cost: Jcost composed with exp -/
noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  simp [Jlog, Jcost_unit0]
  have h : Real.exp t = 1 ↔ t = 0 := Real.exp_eq_one_iff
  exact h

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  simp [Jlog]
  -- Jcost is nonnegative: for x > 0, by AM-GM: x + 1/x ≥ 2, so 1/2(x + 1/x) - 1 ≥ 0
  have hx : 0 < Real.exp t := Real.exp_pos t
  have hamgm : Real.exp t + (Real.exp t)⁻¹ ≥ 2 := by
    have := Real.add_ge_two_mul_sqrt (Real.exp t) (Real.exp t)⁻¹
    · simp at this; exact this
    · exact hx
    · have : 0 < (Real.exp t)⁻¹ := inv_pos.mpr hx
      exact this
  calc
    Jcost (Real.exp t) = (1/2) * (Real.exp t + (Real.exp t)⁻¹) - 1 := rfl
    _ ≥ (1/2) * 2 - 1 := mul_le_mul_of_nonneg_left hamgm (by norm_num)
    _ = 0 := by norm_num

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  -- Jlog(t) = Jcost (exp t) = (exp t + exp (-t))/2 - 1 = cosh t - 1
  have hcosh : HasDerivAt Real.cosh (Real.sinh t) t := Real.hasDerivAt_cosh t
  have h : HasDerivAt (fun s => Real.cosh s - 1) (Real.sinh t) t := hcosh.sub_const 1
  -- Identify Jlog with cosh − 1 pointwise
  have heq : (fun s => Jlog s) = (fun s => Real.cosh s - 1) := by
    funext s
    unfold Jlog
    -- Jcost (exp s) = ((exp s) + (exp s)⁻¹)/2 - 1 and (exp s)⁻¹ = exp (−s)
    simp [Jcost, Real.cosh, Real.exp_neg]
  simpa [heq]

/-- Typeclass for averaging derivation -/
class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

/-- Flog definition -/
noncomputable def Flog (F : ℝ → ℝ) (t : ℝ) : ℝ := F (Real.exp t)

lemma Flog_eq_Jlog_pt {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  Flog F t = Jlog t := by
  dsimp [Flog, Jlog]
  exact AveragingDerivation.agrees t

lemma Flog_eq_Jlog {F : ℝ → ℝ} [AveragingDerivation F] :
  (fun t => Flog F t) = Jlog := by
  funext t; simpa using (Flog_eq_Jlog_pt (F:=F) t)

lemma hasDerivAt_Flog_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  HasDerivAt (Flog F) (Real.sinh t) t := by
  have h := hasDerivAt_Jlog t
  have hfun := (Flog_eq_Jlog (F:=F))
  -- rewrite derivative of Jlog to derivative of Flog via function equality
  simpa [hfun] using h

@[simp] lemma deriv_Flog_zero_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] :
  deriv (Flog F) 0 = 0 := by
  classical
  simpa using (hasDerivAt_Flog_of_derivation (F:=F) 0).deriv

lemma Flog_nonneg_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  0 ≤ Flog F t := by
  have := Jlog_nonneg t
  simpa [Flog_eq_Jlog_pt (F:=F) t] using this

lemma Flog_eq_zero_iff_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  Flog F t = 0 ↔ t = 0 := by
  have := Jlog_eq_zero_iff t
  simpa [Flog_eq_Jlog_pt (F:=F) t] using this

theorem T5_EL_equiv_general {F : ℝ → ℝ} [AveragingDerivation F] :
  deriv (Flog F) 0 = 0 ∧ (∀ t : ℝ, Flog F 0 ≤ Flog F t) ∧ (∀ t : ℝ, Flog F t = 0 ↔ t = 0) := by
  refine ⟨deriv_Flog_zero_of_derivation (F:=F), ?_, ?_⟩
  · intro t; exact Flog_nonneg_of_derivation (F:=F) t
  · intro t; exact Flog_eq_zero_iff_of_derivation (F:=F) t

end Cost
end IndisputableMonolith
