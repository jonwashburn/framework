import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

/-- J(x) expressed as a squared ratio: J(x) = (x-1)²/(2x). -/
lemma Jcost_eq_sq {x : ℝ} (hx : x ≠ 0) :
    Jcost x = (x - 1) ^ 2 / (2 * x) := by
  unfold Jcost
  field_simp [hx]
  ring

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Jcost_eq_sq hx0, Jcost_eq_sq (inv_ne_zero hx0)]
  field_simp [hx0]
  ring

/-- J(x) ≥ 0 for positive x (AM-GM inequality) -/
lemma Jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  have hx0 : x ≠ 0 := hx.ne'
  rw [Jcost_eq_sq hx0]
  positivity

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
by
  intro x hx
  have hAgree : AgreesOnExp F := by
    intro t
    exact le_antisymm (JensenSketch.axis_upper (F:=F) t) (JensenSketch.axis_lower (F:=F) t)
  exact (agree_on_exp_extends (F:=F) hAgree) hx

noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  unfold Jlog Jcost
  rw [Real.cosh_eq, inv_eq_one_div, Real.exp_neg]
  ring

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  have h1 : Jlog = fun t => Real.cosh t - 1 := by
    ext t
    exact Jlog_as_cosh t
  rw [h1]
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

theorem hasDerivAt_Jcost (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Jcost ((1 - x⁻¹ ^ 2) / 2) x := by
  unfold Jcost
  -- The derivative of f(x) = (x + 1/x)/2 - 1 is f'(x) = (1 - 1/x²)/2
  have h1 : HasDerivAt (fun y => y + y⁻¹) (1 + (-(x^2)⁻¹ : ℝ)) x := by
    apply HasDerivAt.add
    · exact hasDerivAt_id x
    · exact hasDerivAt_inv hx
  have h2 : HasDerivAt (fun y => (y + y⁻¹) / 2) ((1 + (-(x^2)⁻¹)) / 2) x :=
    h1.div_const 2
  have h3 : HasDerivAt (fun y => (y + y⁻¹) / 2 - 1) ((1 + (-(x^2)⁻¹)) / 2 - 0) x :=
    h2.sub (hasDerivAt_const x (1 : ℝ))
  have h_eq : (1 + (-(x^2)⁻¹)) / 2 - 0 = (1 - x⁻¹ ^ 2) / 2 := by
    have : (x^2)⁻¹ = x⁻¹ ^ 2 := by rw [inv_pow]
    linarith [this]
  rw [← h_eq]
  exact h3

theorem deriv_Jcost_one : deriv Jcost 1 = 0 := by
  have h : HasDerivAt Jcost ((1 - 1⁻¹ ^ 2) / 2) 1 := hasDerivAt_Jcost 1 (by norm_num)
  simp at h
  exact h.deriv

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog, Jcost]

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t :=
  Jcost_nonneg (Real.exp_pos t)

/-- J(x) > 0 for x ≠ 1 and x > 0. -/
lemma Jcost_pos_of_ne_one (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : 0 < Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Jcost_eq_sq hx0]
  apply div_pos
  · have hne : (x - 1) ≠ 0 := sub_ne_zero.mpr hx1
    exact sq_pos_of_ne_zero hne
  · have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 hx

/-- J(x) = 0 iff x = 1, for positive x. -/
lemma Jcost_eq_zero_iff (x : ℝ) (hx : 0 < x) : Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra h1
    exact absurd h (ne_of_gt (Jcost_pos_of_ne_one x hx h1))
  · intro h
    rw [h]
    exact Jcost_unit0

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hxpos : 0 < Real.exp t := Real.exp_pos t
    have hxne : Real.exp t ≠ 0 := ne_of_gt hxpos
    have hrepr := Jcost_eq_sq hxne
    rw [Jlog, hrepr] at h
    have hden_pos : 0 < 2 * Real.exp t := by
      apply mul_pos
      · norm_num
      · exact hxpos
    have hden_ne : 2 * Real.exp t ≠ 0 := ne_of_gt hden_pos
    rw [div_eq_zero_iff] at h
    cases h with
    | inl h_num =>
      have hexp1 : Real.exp t - 1 = 0 := by nlinarith [sq_nonneg (Real.exp t - 1)]
      have hexp_eq : Real.exp t = 1 := by linarith
      rw [Real.exp_eq_one_iff] at hexp_eq
      exact hexp_eq
    | inr h_den =>
      exact absurd h_den hden_ne
  · intro h
    rw [h]
    exact Jlog_zero


theorem EL_stationary_at_zero : deriv Jlog 0 = 0 := by
  simp

theorem EL_global_min (t : ℝ) : Jlog 0 ≤ Jlog t := by
  simpa [Jlog_zero] using Jlog_nonneg t

/-- From J(x) = 0 and x > 0, conclude x = 1. -/
lemma Jcost_zero_iff_one {x : ℝ} (hx : 0 < x) (h : Jcost x = 0) : x = 1 :=
  (Jcost_eq_zero_iff x hx).mp h

/-! ## Triangle Inequality for J -/

/-- J in terms of cosh: J(exp(t)) = cosh(t) - 1 -/
lemma Jcost_exp_cosh (t : ℝ) : Jcost (Real.exp t) = Real.cosh t - 1 :=
  Jlog_as_cosh t

/-- The sqrt of 2*J gives |log|, which IS a metric. -/
noncomputable def Jmetric (x : ℝ) : ℝ := Real.sqrt (2 * Jcost x)

/-- Jmetric(1) = 0 -/
lemma Jmetric_one : Jmetric 1 = 0 := by
  simp [Jmetric, Jcost_unit0]

/-- Jmetric is symmetric: Jmetric(x) = Jmetric(1/x) -/
lemma Jmetric_symm {x : ℝ} (hx : 0 < x) : Jmetric x = Jmetric x⁻¹ := by
  simp only [Jmetric, Jcost_symm hx]

/-- Jmetric is non-negative -/
lemma Jmetric_nonneg {x : ℝ} (_ : 0 < x) : 0 ≤ Jmetric x :=
  Real.sqrt_nonneg _

/-- Key identity: 2(cosh(t) - 1) = 4sinh²(t/2)

    Proof: cosh(2u) = cosh²(u) + sinh²(u), and cosh²(u) = 1 + sinh²(u).
    So cosh(2u) = 1 + 2sinh²(u), hence cosh(2u) - 1 = 2sinh²(u). -/
lemma cosh_minus_one_eq (t : ℝ) : 2 * (Real.cosh t - 1) = 4 * Real.sinh (t / 2) ^ 2 := by
  -- Use the double-angle formula: cosh(2u) = cosh²(u) + sinh²(u)
  have h := Real.cosh_two_mul (t / 2)
  -- h : cosh(2*(t/2)) = cosh²(t/2) + sinh²(t/2)
  simp only [two_mul, add_halves] at h
  -- So h : cosh(t) = cosh²(t/2) + sinh²(t/2)
  -- From cosh²(t/2) - sinh²(t/2) = 1, we get cosh²(t/2) = 1 + sinh²(t/2)
  have h2 := Real.cosh_sq_sub_sinh_sq (t / 2)
  have h3 : Real.cosh (t / 2) ^ 2 = 1 + Real.sinh (t / 2) ^ 2 := by linarith
  -- Substitute: cosh(t) = (1 + sinh²(t/2)) + sinh²(t/2) = 1 + 2sinh²(t/2)
  -- So cosh(t) - 1 = 2sinh²(t/2)
  calc 2 * (Real.cosh t - 1)
      = 2 * ((Real.cosh (t / 2) ^ 2 + Real.sinh (t / 2) ^ 2) - 1) := by rw [h]
    _ = 2 * (((1 + Real.sinh (t / 2) ^ 2) + Real.sinh (t / 2) ^ 2) - 1) := by rw [h3]
    _ = 2 * (2 * Real.sinh (t / 2) ^ 2) := by ring
    _ = 4 * Real.sinh (t / 2) ^ 2 := by ring

/-- Jmetric in terms of sinh: Jmetric(exp(t)) = 2|sinh(t/2)| -/
lemma Jmetric_exp_sinh (t : ℝ) : Jmetric (Real.exp t) = 2 * |Real.sinh (t / 2)| := by
  unfold Jmetric
  rw [Jcost_exp_cosh, cosh_minus_one_eq]
  -- sqrt(4 * sinh²(t/2)) = sqrt(4) * |sinh(t/2)| = 2 * |sinh(t/2)|
  rw [show (4 : ℝ) * Real.sinh (t / 2) ^ 2 = (2 * Real.sinh (t / 2)) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ### Note on Triangle Inequality

The function `Jmetric(x) = sqrt(2 * Jcost(x))` does NOT satisfy the triangle inequality
under multiplication. Numerical counterexample:
- Jmetric(6) ≈ 2.04 > Jmetric(2) + Jmetric(3) ≈ 1.86

This is expected: J-cost measures the "recognition strain" of a ratio, and strain
compounds superlinearly when multiplying far-from-unity ratios.

The key inequality that DOES hold is the d'Alembert identity, which gives
`Jcost_submult`: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y). -/

/-- **Standard Analysis**: Evaluation of Jmetric at specific points. -/
theorem Jmetric_val_6 : Jmetric 6 = Real.sqrt (25 / 6) := by
  unfold Jmetric Jcost
  norm_num

theorem Jmetric_val_2 : Jmetric 2 = Real.sqrt (1 / 2) := by
  unfold Jmetric Jcost
  norm_num

theorem Jmetric_val_3 : Jmetric 3 = Real.sqrt (4 / 3) := by
  unfold Jmetric Jcost
  norm_num

theorem sqrt_triangle_violation : Real.sqrt (25 / 6) > Real.sqrt (1 / 2) + Real.sqrt (4 / 3) := by
  have h1 : 0 ≤ Real.sqrt (1 / 2) + Real.sqrt (4 / 3) := by positivity
  change Real.sqrt (1 / 2) + Real.sqrt (4 / 3) < Real.sqrt (25 / 6)
  rw [← Real.sqrt_sq h1]
  rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  rw [add_sq, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
  norm_num
  -- Goal: 1 / 2 + 2 * (√2 / √3) + 4 / 3 < 25 / 6
  suffices 2 * (Real.sqrt 2 / Real.sqrt 3) < 7 / 3 by linarith
  have h_lhs : 2 * (Real.sqrt 2 / Real.sqrt 3) = Real.sqrt (8 / 3) := by
    rw [← Real.sqrt_div (by norm_num) 3]
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h_rhs : (7 / 3 : ℝ) = Real.sqrt (49 / 9) := by
    rw [Real.sqrt_div (by norm_num) 9]
    norm_num
  rw [h_lhs, h_rhs]
  rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  norm_num

/-- **DEPRECATED**: The naive triangle inequality does NOT hold for Jmetric.
    Use `Jcost_submult` instead, which gives a valid submultiplicativity bound. -/
theorem Jmetric_triangle_FALSE {x y : ℝ} (_hx : 0 < x) (_hy : 0 < y) :
    ¬ (∀ a b : ℝ, 0 < a → 0 < b → Jmetric (a * b) ≤ Jmetric a + Jmetric b) := by
  intro h
  -- Counterexample: a = 2, b = 3
  let a : ℝ := 2
  let b : ℝ := 3
  have ha : 0 < a := by norm_num
  have hb : 0 < b := by norm_num
  have h_tri := h a b ha hb
  rw [show a * b = 6 by norm_num, Jmetric_val_6, Jmetric_val_2, Jmetric_val_3] at h_tri
  have h_viol := sqrt_triangle_violation
  linarith

/-- **DEPRECATED**: The "weak triangle" J(xy) ≤ 2(J(x)+J(y)) + 2√(J(x)J(y)) is FALSE.

    Counterexample: x = y = 10
    - J(100) ≈ 49.005
    - 2(J(10) + J(10)) + 2√(J(10)·J(10)) = 2(4.05 + 4.05) + 2·4.05 ≈ 24.3
    - 49.005 > 24.3

    Use `Jcost_submult` instead: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y), which IS proved. -/
theorem Jcost_weak_triangle_FALSE :
    ¬ (∀ x y : ℝ, 0 < x → 0 < y →
      Jcost (x * y) ≤ 2 * (Jcost x + Jcost y) + 2 * Real.sqrt (Jcost x * Jcost y)) := by
  intro h
  -- Counterexample: x = y = 10, J(100) > 2(J(10)+J(10)) + 2*sqrt(J(10)*J(10))
  -- J(100) = (100 + 1/100)/2 - 1 = 49.005
  -- J(10) = (10 + 0.1)/2 - 1 = 4.05
  -- RHS = 2*(4.05 + 4.05) + 2*sqrt(4.05*4.05) = 16.2 + 8.1 = 24.3
  -- 49.005 > 24.3 is TRUE, not ≤, so the inequality fails
  have hc := h 10 10 (by norm_num) (by norm_num)
  -- The claim asserts ≤ but the counterexample shows >
  -- J(100) = 49.005, RHS = 24.3, so 49.005 > 24.3
  simp only [Jcost] at hc
  nlinarith [sq_nonneg (10 : ℝ), Real.sqrt_nonneg (Jcost 10 * Jcost 10)]

/-- The d'Alembert identity: J(xy) + J(x/y) = 2J(x) + 2J(y) + 2J(x)J(y) -/
theorem dalembert_identity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) + Jcost (x / y) = 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hxdy : x / y ≠ 0 := div_ne_zero hx0 hy0
  simp only [Jcost_eq_sq hxy, Jcost_eq_sq hxdy, Jcost_eq_sq hx0, Jcost_eq_sq hy0]
  field_simp
  ring

/-- From d'Alembert: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y) since J(x/y) ≥ 0 -/
lemma Jcost_submult {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) ≤ 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := by
  have h := dalembert_identity hx hy
  have hnonneg : 0 ≤ Jcost (x / y) := Jcost_nonneg (div_pos hx hy)
  linarith

/-- Bound on J product: J(xy) ≤ 2*(1 + J(x))*(1 + J(y)) - 2
    This follows from d'Alembert since (1+J(x))(1+J(y)) = 1 + J(x) + J(y) + J(x)J(y) -/
lemma Jcost_prod_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) ≤ 2 * (1 + Jcost x) * (1 + Jcost y) - 2 := by
  have h := Jcost_submult hx hy
  -- 2*(1+J(x))*(1+J(y)) - 2 = 2*(1 + J(x) + J(y) + J(x)*J(y)) - 2
  --                        = 2 + 2*J(x) + 2*J(y) + 2*J(x)*J(y) - 2
  --                        = 2*J(x) + 2*J(y) + 2*J(x)*J(y)
  calc Jcost (x * y) ≤ 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := h
    _ = 2 * (1 + Jcost x) * (1 + Jcost y) - 2 := by ring

end Cost
end IndisputableMonolith
