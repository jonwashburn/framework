import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Type where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Jcost
  have : (x + x⁻¹) = (x⁻¹ + (x⁻¹)⁻¹) := by
    field_simp [hx0]
    ring
  simp [this]

/-- Jcost is non-negative for positive arguments -/
lemma Jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  unfold Jcost
  -- By AM-GM inequality: x + x⁻¹ ≥ 2, so (x + x⁻¹)/2 ≥ 1, thus (x + x⁻¹)/2 - 1 ≥ 0
  -- Direct proof: x + x⁻¹ ≥ 2 iff (x - 1)² ≥ 0 (after clearing denominators)
  suffices x + x⁻¹ ≥ 2 by linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  -- Multiply both sides by x > 0: x² + 1 ≥ 2x iff (x-1)² ≥ 0
  nlinarith [sq_nonneg (x - 1), mul_inv_cancel₀ hx0]

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : AgreesOnExp F

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t; rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

instance : SymmUnit Jcost :=
  { symmetric := by
      intro x hx
      simp [Jcost_symm (x:=x) hx]
    , unit0 := Jcost_unit0 }

instance : AveragingDerivation Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , agrees := Jcost_agrees_on_exp }

instance : JensenSketch Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , axis_upper := by intro t; exact le_of_eq rfl
  , axis_lower := by intro t; exact le_of_eq rfl }

/-! ## Small-strain Taylor expansion

For `x = 1 + ε` with `|ε| < 1`, we establish the quadratic leading term
`J(1+ε) = ½ε² + O(ε³)`, which is central to Axiom A4 in the value functional.
The strategy: write `1+ε = exp(ln(1+ε))`, expand `ln(1+ε) ≈ ε - ε²/2 + …`,
then use the cosh series to obtain the result.
-/

/-!
Note (2025-12-20): for `Jcost(x) := (x + x⁻¹)/2 - 1`, there is a *closed form* at `x = 1 + ε`:

`Jcost(1+ε) = ε^2 / (2*(1+ε))`.

So the “quadratic + cubic remainder” bounds follow by elementary algebra, without any Taylor-series
machinery or API-sensitive calculus lemmas.
-/

lemma Jcost_one_plus_eps_closed_form (ε : ℝ) (hpos : 0 < 1 + ε) :
    Jcost (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
  have hne : (1 + ε) ≠ 0 := ne_of_gt hpos
  unfold Jcost
  field_simp [hne]
  ring

lemma Jcost_one_plus_eps_quadratic (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 2) :
    ∃ (c : ℝ), Jcost (1 + ε) = ε ^ 2 / 2 + c * ε ^ 3 ∧ |c| ≤ 2 := by
  have hbounds : (-( (1 : ℝ) / 2) ≤ ε) ∧ (ε ≤ (1 : ℝ) / 2) := (abs_le.mp hε)
  have hpos : 0 < 1 + ε := by linarith [hbounds.1]

  refine ⟨-(1 / (2 * (1 + ε))), ?_, ?_⟩
  · -- algebraic identity: J = ε^2/2 + c*ε^3 with c = -1/(2(1+ε))
    have hClosed := Jcost_one_plus_eps_closed_form (ε := ε) hpos
    -- rewrite using the closed form and clear denominators
    have hne : (1 + ε) ≠ 0 := ne_of_gt hpos
    -- `simp` won't see the structure automatically; use `field_simp` + `ring`
    -- to show: ε^2/(2(1+ε)) = ε^2/2 - ε^3/(2(1+ε)).
    -- (which is exactly ε^2/2 + (-(1/(2(1+ε))))*ε^3)
    -- First, normalize the RHS.
    -- Note: `simp` will turn `(-a) * b` into `-(a*b)` which is fine under `ring`.
    -- We'll do it in one shot.
    -- Replace `Jcost (1+ε)` with the closed form:
    rw [hClosed]
    field_simp [hne]
    ring
  · -- bound |c| ≤ 2 under |ε| ≤ 1/2
    have hLower : (1 : ℝ) / 2 ≤ 1 + ε := by linarith [hbounds.1]
    have hDenPos : 0 < (2 * (1 + ε) : ℝ) := by nlinarith [hpos]
    -- |-(1/(2(1+ε)))| = 1/(2(1+ε)) since denominator is positive
    have hAbs : |-(1 / (2 * (1 + ε)))| = 1 / (2 * (1 + ε)) := by
      have hRecPos : 0 < (1 / (2 * (1 + ε)) : ℝ) := by
        exact one_div_pos.mpr hDenPos
      -- avoid `simpa`/simp-side-goals: do it as a small calc
      calc
        |-(1 / (2 * (1 + ε)))|
            = |(1 / (2 * (1 + ε)))| := by simp
        _   = (1 / (2 * (1 + ε))) := abs_of_pos hRecPos
    rw [hAbs]
    -- Since 1 ≤ 2*(1+ε), we have 1/(2*(1+ε)) ≤ 1 ≤ 2
    have hDenGe1 : (1 : ℝ) ≤ 2 * (1 + ε) := by nlinarith [hLower]
    have hRecLe1 : (1 / (2 * (1 + ε)) : ℝ) ≤ 1 := by
      have h0 : (0 : ℝ) < (1 : ℝ) := by norm_num
      have := one_div_le_one_div_of_le h0 hDenGe1
      simpa using this
    linarith [hRecLe1]

lemma Jcost_small_strain_bound (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 10) :
    |Jcost (1 + ε) - ε ^ 2 / 2| ≤ ε ^ 2 / 10 := by
  -- Work with symmetric bounds from the absolute-value hypothesis.
  have hbounds : (-( (1 : ℝ) / 10) ≤ ε) ∧ (ε ≤ (1 : ℝ) / 10) := (abs_le.mp hε)
  have hpos : 0 < 1 + ε := by linarith [hbounds.1]
  have hne : (1 + ε) ≠ 0 := ne_of_gt hpos
  have hAbsLe : |ε| ≤ (1 : ℝ) / 10 := by simpa using hε

  -- Rewrite J via the exact closed form.
  have hClosed := Jcost_one_plus_eps_closed_form (ε := ε) hpos
  -- Convert to an explicit difference.
  have hDiff :
      Jcost (1 + ε) - ε ^ 2 / 2 = -(ε ^ 3) / (2 * (1 + ε)) := by
    -- Start from the closed form and clear denominators.
    rw [hClosed]
    field_simp [hne]
    ring
  -- Now take absolute values.
  rw [hDiff]
  have hDenPos : 0 < (2 * (1 + ε) : ℝ) := by nlinarith [hpos]
  -- `|-(a)/b| = |a|/|b|`, and with b>0 we have |b|=b.
  have hAbs :
      |-(ε ^ 3) / (2 * (1 + ε))| = |ε ^ 3| / (2 * (1 + ε)) := by
    simp [abs_div, abs_of_pos hDenPos]
  rw [hAbs]

  -- Lower bound for the denominator: 1+ε ≥ 9/10
  have hOnePlusLower : (9 : ℝ) / 10 ≤ 1 + ε := by linarith [hbounds.1]
  have hDenLower : (9 : ℝ) / 5 ≤ 2 * (1 + ε) := by nlinarith [hOnePlusLower]
  -- Hence 1/(2(1+ε)) ≤ 5/9
  have hRecUpper : (1 / (2 * (1 + ε)) : ℝ) ≤ (5 : ℝ) / 9 := by
    have h0' : (0 : ℝ) < (9 : ℝ) / 5 := by norm_num
    have := one_div_le_one_div_of_le h0' hDenLower
    -- 1 / (9/5) = 5/9
    simpa [one_div, div_eq_mul_inv] using this

  -- Bound |ε^3| = |ε|^3, then apply the reciprocal bound.
  have hPow : |ε ^ 3| = |ε| ^ 3 := by
    simpa using (abs_pow ε 3)

  rw [hPow]
  -- Write as |ε|^3 * (1/(2(1+ε))) and bound by |ε|^3*(5/9).
  have hStep1 :
      (|ε| ^ 3) / (2 * (1 + ε)) ≤ (|ε| ^ 3) * ((5 : ℝ) / 9) := by
    -- division = multiplication by reciprocal; multiply both sides by nonneg |ε|^3
    have hNonneg : 0 ≤ (|ε| ^ 3 : ℝ) := by
      exact pow_nonneg (abs_nonneg ε) 3
    -- (|ε|^3) * (1/(2(1+ε))) ≤ (|ε|^3) * (5/9)
    have := mul_le_mul_of_nonneg_left hRecUpper hNonneg
    -- normalize
    simpa [div_eq_mul_inv, mul_assoc] using this

  have hStep2 :
      (|ε| ^ 3) * ((5 : ℝ) / 9) ≤ (|ε| ^ 2) / 10 := by
    -- Use |ε| ≤ 1/10 and 5/9 ≤ 1 to get an easy bound.
    have h59 : (5 : ℝ) / 9 ≤ 1 := by norm_num
    have hAbsTimes : |ε| * ((5 : ℝ) / 9) ≤ (1 : ℝ) / 10 := by
      have hNonneg : 0 ≤ (5 : ℝ) / 9 := by norm_num
      have h1 : |ε| * ((5 : ℝ) / 9) ≤ ((1 : ℝ) / 10) * ((5 : ℝ) / 9) :=
        mul_le_mul_of_nonneg_right hAbsLe hNonneg
      have h2 : ((1 : ℝ) / 10) * ((5 : ℝ) / 9) ≤ (1 : ℝ) / 10 := by
        -- (1/10)*(5/9) = 1/18 < 1/10
        norm_num
      exact le_trans h1 h2
    -- Now: |ε|^3*(5/9) = |ε|^2 * (|ε|*(5/9)) ≤ |ε|^2 * (1/10)
    -- and |ε|^2 = ε^2.
    have hNonneg2 : 0 ≤ (|ε| ^ 2 : ℝ) := by
      exact pow_nonneg (abs_nonneg ε) 2
    have := mul_le_mul_of_nonneg_left hAbsTimes hNonneg2
    -- normalize powers: |ε|^2 * (|ε| * (5/9)) = |ε|^3 * (5/9)
    -- and |ε|^2 * (1/10) = |ε|^2 / 10
    -- then replace |ε|^2 with ε^2 at the end.
    -- `ring` handles the algebraic reshuffle.
    -- First massage into the exact shape.
    -- Normalize both sides to the target shape.
    -- Left: |ε|^2 * (|ε|*(5/9)) = |ε|^3*(5/9)
    have hA :
        (|ε| ^ 2) * (|ε| * ((5 : ℝ) / 9)) = (|ε| ^ 3) * ((5 : ℝ) / 9) := by
      -- `|ε| ^ 3 = (|ε| ^ 2) * |ε|`
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
    -- Right: |ε|^2 * (1/10) = |ε|^2 / 10
    have hB : (|ε| ^ 2) * ((1 : ℝ) / 10) = (|ε| ^ 2) / 10 := by
      simp [div_eq_mul_inv]
    -- The inequality `this` is: (|ε|^2) * (|ε|*(5/9)) ≤ (|ε|^2) * (1/10).
    -- Rewrite with hA/hB and finish.
    have : (|ε| ^ 3) * ((5 : ℝ) / 9) ≤ (|ε| ^ 2) / 10 := by
      -- Start from `this` and rewrite both sides.
      -- (We use `calc` for robustness.)
      calc
        (|ε| ^ 3) * ((5 : ℝ) / 9)
            = (|ε| ^ 2) * (|ε| * ((5 : ℝ) / 9)) := by
                -- reverse of hA
                simpa [hA] using (hA.symm)
        _   ≤ (|ε| ^ 2) * ((1 : ℝ) / 10) := this
        _   = (|ε| ^ 2) / 10 := hB
    exact this

  -- Combine the two steps.
  have hMain : (|ε| ^ 3) / (2 * (1 + ε)) ≤ (|ε| ^ 2) / 10 := by
    exact le_trans hStep1 hStep2

  -- Finally, replace |ε|^2 with ε^2.
  have hAbsSq : (|ε| ^ 2 : ℝ) = ε ^ 2 := by
    -- since even power
    simp [pow_two]
  -- apply the bound and rewrite
  -- (goal is ≤ ε^2/10)
  simpa [hAbsSq] using hMain

end Cost
end IndisputableMonolith
