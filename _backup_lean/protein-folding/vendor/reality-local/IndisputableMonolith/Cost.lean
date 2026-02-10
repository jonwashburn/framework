import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
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

/-- J(x) ≥ 0 for positive x (AM-GM inequality) -/
lemma Jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
  simp only [Jcost]
  -- (x + 1/x)/2 - 1 ≥ 0  ⟺  x + 1/x ≥ 2  ⟺  (x-1)² ≥ 0 (after mult by x)
  have h : 0 ≤ (x - 1)^2 / x := by positivity
  calc (x + x⁻¹) / 2 - 1 = ((x - 1)^2 / x) / 2 := by field_simp; ring
    _ ≥ 0 := by positivity

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

lemma even_on_log_of_symm {F : ℝ → ℝ} [SymmUnit F] (t : ℝ) :
    F (Real.exp t) = F (Real.exp (-t)) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  simpa [Real.exp_neg] using (SymmUnit.symmetric (F:=F) hx)

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

theorem agrees_on_exp_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
    AgreesOnExp F := by
  intro t
  have h₁ := AveragingBounds.upper (F:=F) t
  have h₂ := AveragingBounds.lower (F:=F) t
  have : F (Real.exp t) = Jcost (Real.exp t) := le_antisymm h₁ h₂
  simpa using this

theorem F_eq_J_on_pos_alt (F : ℝ → ℝ)
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : ∃ t, Real.exp t = x := ⟨Real.log x, by simpa using Real.exp_log hx⟩
  rcases this with ⟨t, rfl⟩
  simpa using hAgree t

instance (priority := 90) averagingDerivation_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
    AveragingDerivation F :=
  { toSymmUnit := (inferInstance : SymmUnit F)
  , agrees := agrees_on_exp_of_bounds (F:=F) }

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
    AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

class LogModel (G : ℝ → ℝ) where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simp
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        simpa using (LogModel.even_log (G:=G) (Real.log x)).symm
      simpa [hlog]
        using he
    , unit0 := by
      dsimp [F_ofLog]
      simpa [Real.log_one] using (LogModel.base0 (G:=G)) }

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

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

theorem F_eq_J_on_pos {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  agree_on_exp_extends (F:=F) hAgree

theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos_of_derivation F

noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  unfold Jlog Jcost
  rw [Real.cosh_eq, inv_eq_one_div, Real.exp_neg]
  ring

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  -- Jlog t = cosh t - 1, and d/dt(cosh t - 1) = sinh t
  have h1 : Jlog = fun t => Real.cosh t - 1 := by
    ext t
    exact Jlog_as_cosh t
  rw [h1]
  -- HasDerivAt (cosh - 1) (sinh t) t
  have h_cosh : HasDerivAt Real.cosh (Real.sinh t) t := Real.hasDerivAt_cosh t
  have h_const : HasDerivAt (fun _ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h_sub := h_cosh.sub h_const
  simp at h_sub
  exact h_sub

@[simp] lemma hasDerivAt_Jlog_zero : HasDerivAt Jlog 0 0 := by
  simpa using (hasDerivAt_Jlog 0)

@[simp] lemma deriv_Jlog_zero : deriv Jlog 0 = 0 := by
  classical
  simpa using (hasDerivAt_Jlog_zero).deriv

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  dsimp [Jlog]
  have : Jcost 1 = 0 := Jcost_unit0
  simpa [Real.exp_zero] using this

private lemma Jcost_eq_sq_div (x : ℝ) (hx : x ≠ 0) :
  Jcost x = (x - 1)^2 / (2 * x) := by
  unfold Jcost
  field_simp [hx]
  ring

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  -- Use the identity J(x) = (x - 1)^2 / (2x) with x = exp t
  have hxpos : 0 < Real.exp t := Real.exp_pos t
  have hxne : Real.exp t ≠ 0 := ne_of_gt hxpos
  have hrepr := Jcost_eq_sq_div (Real.exp t) hxne
  have hnum : 0 ≤ (Real.exp t - 1)^2 := by exact sq_nonneg _
  have hden : 0 ≤ 2 * Real.exp t := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg h2 (le_of_lt hxpos)
  simpa [Jlog, hrepr] using (div_nonneg hnum hden)

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  constructor
  · intro h
    -- Jlog t = (exp t - 1)^2 / (2 * exp t) = 0 implies exp t = 1 implies t = 0
    have hxpos : 0 < Real.exp t := Real.exp_pos t
    have hxne : Real.exp t ≠ 0 := ne_of_gt hxpos
    have hrepr := Jcost_eq_sq_div (Real.exp t) hxne
    rw [Jlog] at h
    rw [hrepr] at h
    -- (exp t - 1)^2 / (2 * exp t) = 0
    have hden_pos : 0 < 2 * Real.exp t := by
      apply mul_pos
      · norm_num
      · exact hxpos
    have hden_ne : 2 * Real.exp t ≠ 0 := ne_of_gt hden_pos
    rw [div_eq_zero_iff] at h
    cases h with
    | inl h_num =>
      -- (exp t - 1)^2 = 0 implies exp t = 1
      have hexp1 : Real.exp t - 1 = 0 := by nlinarith [sq_nonneg (Real.exp t - 1)]
      have hexp_eq : Real.exp t = 1 := by linarith
      rw [Real.exp_eq_one_iff] at hexp_eq
      exact hexp_eq
    | inr h_den =>
      -- 2 * exp t = 0 is impossible
      exact absurd h_den hden_ne
  · intro h
    rw [h]
    exact Jlog_zero

theorem EL_stationary_at_zero : deriv Jlog 0 = 0 := by
  simp

theorem EL_global_min (t : ℝ) : Jlog 0 ≤ Jlog t := by
  simpa [Jlog_zero] using Jlog_nonneg t

end Cost
end IndisputableMonolith
