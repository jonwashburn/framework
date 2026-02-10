import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import IndisputableMonolith.Cost

open IndisputableMonolith

/-!
# Functional Equation Helpers for T5

This module provides lemmas for the T5 cost uniqueness proof.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-- Log-coordinate reparametrization: `G_F t = F (exp t)` -/
@[simp] noncomputable def G (F : ℝ → ℝ) (t : ℝ) : ℝ := F (Real.exp t)

/-- Convenience reparametrization: `H_F t = G_F t + 1`. -/
@[simp] noncomputable def H (F : ℝ → ℝ) (t : ℝ) : ℝ := G F t + 1

/-- The cosh-type functional identity for `G_F`. -/
def CoshAddIdentity (F : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ,
    G F (t+u) + G F (t-u) = 2 * (G F t * G F u) + 2 * (G F t + G F u)

/-- Direct cosh-add identity on a function. -/
def DirectCoshAdd (Gf : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ,
    Gf (t+u) + Gf (t-u) = 2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)

lemma CoshAddIdentity_implies_DirectCoshAdd (F : ℝ → ℝ)
  (h : CoshAddIdentity F) :
  DirectCoshAdd (G F) := h

lemma G_even_of_reciprocal_symmetry
  (F : ℝ → ℝ)
  (hSymm : ∀ {x : ℝ}, 0 < x → F x = F x⁻¹) :
  Function.Even (G F) := by
  intro t
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hrec : Real.exp (-t) = (Real.exp t)⁻¹ := by simp [Real.exp_neg]
  simp [G, hrec, hSymm hpos]

lemma G_zero_of_unit (F : ℝ → ℝ) (hUnit : F 1 = 0) : G F 0 = 0 := by
  simpa [G] using hUnit

theorem Jcost_G_eq_cosh_sub_one (t : ℝ) : G Cost.Jcost t = Real.cosh t - 1 := by
  simp only [G, Jcost]
  -- Jcost(exp t) = (exp t + exp(-t))/2 - 1 = cosh t - 1
  have h1 : (Real.exp t)⁻¹ = Real.exp (-t) := by simp [Real.exp_neg]
  rw [h1, Real.cosh_eq]

theorem Jcost_cosh_add_identity : CoshAddIdentity Cost.Jcost := by
  intro t u
  simp only [G, Jcost]
  -- Use exp(t+u) = exp(t)*exp(u) and exp(t-u) = exp(t)/exp(u)
  have he1 : Real.exp (t + u) = Real.exp t * Real.exp u := Real.exp_add t u
  have he2 : Real.exp (t - u) = Real.exp t / Real.exp u := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring
  have hpos_t : Real.exp t > 0 := Real.exp_pos t
  have hpos_u : Real.exp u > 0 := Real.exp_pos u
  have hne_t : Real.exp t ≠ 0 := hpos_t.ne'
  have hne_u : Real.exp u ≠ 0 := hpos_u.ne'
  rw [he1, he2]
  field_simp
  ring

theorem even_deriv_at_zero (H : ℝ → ℝ)
  (h_even : Function.Even H) (h_diff : DifferentiableAt ℝ H 0) : deriv H 0 = 0 := by
  -- For even functions, the derivative at 0 is 0
  let negFun : ℝ → ℝ := fun x => -x
  have h1 : deriv H 0 = deriv (H ∘ negFun) 0 := by
    congr 1
    ext x
    simp only [Function.comp_apply, negFun]
    exact (h_even x).symm
  have h2 : deriv (H ∘ negFun) 0 = -deriv H 0 := by
    have hd : DifferentiableAt ℝ negFun 0 := differentiable_neg.differentiableAt
    have h_diff_neg : DifferentiableAt ℝ H (negFun 0) := by simp [negFun]; exact h_diff
    have hchain := deriv_comp (x := (0 : ℝ)) h_diff_neg hd
    rw [hchain]
    simp only [negFun, neg_zero]
    have hdn : deriv negFun 0 = -1 := congrFun deriv_neg' 0
    rw [hdn]
    ring
  rw [h1] at h2
  linarith

lemma dAlembert_even
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) :
  Function.Even H := by
  intro u
  have h := h_dAlembert 0 u
  simpa [h_one, zero_add, sub_eq_add_neg, two_mul] using h

/-! ## ODE Uniqueness Infrastructure -/

/-- Helper: derivative of exp(-s) is -exp(-s). -/
lemma deriv_exp_neg (t : ℝ) : deriv (fun s => Real.exp (-s)) t = -Real.exp (-t) := by
  have h := Real.hasDerivAt_exp (-t)
  have hc : HasDerivAt (fun s => -s) (-1) t := by
    have := hasDerivAt_neg (x := t)
    simp at this ⊢
    exact this
  have hcomp := h.comp t hc
  simp at hcomp
  exact hcomp.deriv

/-- Diagonalization of the ODE f'' = f into f' ± f components. -/
lemma ode_diagonalization (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = f t) :
    (∀ t, deriv (fun s => deriv f s - f s) t = -(deriv f t - f t)) ∧
    (∀ t, deriv (fun s => deriv f s + f s) t = deriv f t + f t) := by
  have h_diff1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_contdiff : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_diff_deriv : Differentiable ℝ (deriv f) := h_deriv_contdiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  constructor
  · intro t
    have h1 : deriv (fun s => deriv f s - f s) t = deriv (deriv f) t - deriv f t := by
      apply deriv_sub h_diff_deriv.differentiableAt h_diff1.differentiableAt
    rw [h1, h_ode t]
    ring
  · intro t
    have h2 : deriv (fun s => deriv f s + f s) t = deriv (deriv f) t + deriv f t := by
      apply deriv_add h_diff_deriv.differentiableAt h_diff1.differentiableAt
    rw [h2, h_ode t]
    ring

/-- If g' = -g and g(0) = 0, then g = 0. -/
lemma deriv_neg_self_zero (g : ℝ → ℝ)
    (h_diff : Differentiable ℝ g)
    (h_deriv : ∀ t, deriv g t = -g t)
    (h_g0 : g 0 = 0) :
    ∀ t, g t = 0 := by
  have h_const : ∀ t, deriv (fun s => g s * Real.exp s) t = 0 := by
    intro t
    have h1 : deriv (fun s => g s * Real.exp s) t =
              deriv g t * Real.exp t + g t * deriv Real.exp t := by
      apply deriv_mul h_diff.differentiableAt Real.differentiable_exp.differentiableAt
    rw [h1, Real.deriv_exp, h_deriv t]
    ring
  have h_diff_prod : Differentiable ℝ (fun s => g s * Real.exp s) := by
    apply Differentiable.mul h_diff Real.differentiable_exp
  have h_is_const := is_const_of_deriv_eq_zero h_diff_prod h_const
  intro t
  specialize h_is_const t 0
  simp only [Real.exp_zero, mul_one] at h_is_const
  have h_exp_pos : Real.exp t > 0 := Real.exp_pos t
  have h_exp_ne : Real.exp t ≠ 0 := h_exp_pos.ne'
  have h_eq : g t * Real.exp t = g 0 := h_is_const
  calc g t = g t * Real.exp t / Real.exp t := by field_simp
    _ = g 0 / Real.exp t := by rw [h_eq]
    _ = 0 / Real.exp t := by rw [h_g0]
    _ = 0 := by simp

/-- If h' = h and h(0) = 0, then h = 0. -/
lemma deriv_pos_self_zero (h : ℝ → ℝ)
    (h_diff : Differentiable ℝ h)
    (h_deriv : ∀ t, deriv h t = h t)
    (h_h0 : h 0 = 0) :
    ∀ t, h t = 0 := by
  have h_const : ∀ t, deriv (fun s => h s * Real.exp (-s)) t = 0 := by
    intro t
    have h1 : deriv (fun s => h s * Real.exp (-s)) t =
              deriv h t * Real.exp (-t) + h t * deriv (fun s => Real.exp (-s)) t := by
      apply deriv_mul h_diff.differentiableAt
      exact (Real.differentiable_exp.comp differentiable_neg).differentiableAt
    rw [h1, deriv_exp_neg, h_deriv t]
    ring
  have h_diff_prod : Differentiable ℝ (fun s => h s * Real.exp (-s)) := by
    apply Differentiable.mul h_diff
    exact Real.differentiable_exp.comp differentiable_neg
  have h_is_const := is_const_of_deriv_eq_zero h_diff_prod h_const
  intro t
  specialize h_is_const t 0
  simp only [neg_zero, Real.exp_zero, mul_one] at h_is_const
  have h_exp_pos : Real.exp (-t) > 0 := Real.exp_pos (-t)
  have h_exp_ne : Real.exp (-t) ≠ 0 := h_exp_pos.ne'
  have h_eq : h t * Real.exp (-t) = h 0 := h_is_const
  calc h t = h t * Real.exp (-t) / Real.exp (-t) := by field_simp
    _ = h 0 / Real.exp (-t) := by rw [h_eq]
    _ = 0 / Real.exp (-t) := by rw [h_h0]
    _ = 0 := by simp

/-- **Theorem (ODE Zero Uniqueness)**: The unique solution to f'' = f with f(0) = f'(0) = 0 is f = 0. -/
theorem ode_zero_uniqueness (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = f t)
    (h_f0 : f 0 = 0)
    (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = 0 := by
  have ⟨h_minus, h_plus⟩ := ode_diagonalization f h_diff2 h_ode
  have h_diff1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_contdiff : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_diff_deriv : Differentiable ℝ (deriv f) := h_deriv_contdiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  let g := fun s => deriv f s - f s
  let hf := fun s => deriv f s + f s
  have hg_diff : Differentiable ℝ g := h_diff_deriv.sub h_diff1
  have hh_diff : Differentiable ℝ hf := h_diff_deriv.add h_diff1
  have hg0 : g 0 = 0 := by simp [g, h_f0, h_f'0]
  have hh0 : hf 0 = 0 := by simp [hf, h_f0, h_f'0]
  have hg_deriv : ∀ t, deriv g t = -g t := h_minus
  have hh_deriv : ∀ t, deriv hf t = hf t := h_plus
  have hg_zero := deriv_neg_self_zero g hg_diff hg_deriv hg0
  have hh_zero := deriv_pos_self_zero hf hh_diff hh_deriv hh0
  intro t
  have hgt := hg_zero t
  have hht := hh_zero t
  simp only [g, hf] at hgt hht
  linarith

theorem cosh_second_deriv_eq : ∀ t, deriv (deriv (fun x => Real.cosh x)) t = Real.cosh t := by
  intro t
  have h1 : deriv (fun x => Real.cosh x) = Real.sinh := Real.deriv_cosh
  rw [h1]
  have h2 : deriv Real.sinh = Real.cosh := Real.deriv_sinh
  exact congrFun h2 t

theorem cosh_initials : Real.cosh 0 = 1 ∧ deriv (fun x => Real.cosh x) 0 = 0 := by
  constructor
  · simp [Real.cosh_zero]
  · have h := Real.deriv_cosh
    simp only [h, Real.sinh_zero]

/-- **Theorem (ODE Cosh Uniqueness)**: The unique solution to H'' = H with H(0) = 1, H'(0) = 0 is cosh. -/
theorem ode_cosh_uniqueness_contdiff (H : ℝ → ℝ)
    (h_diff : ContDiff ℝ 2 H)
    (h_ode : ∀ t, deriv (deriv H) t = H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0) :
    ∀ t, H t = Real.cosh t := by
  let g := fun t => H t - Real.cosh t
  have hg_diff : ContDiff ℝ 2 g := h_diff.sub Real.contDiff_cosh
  have hg_ode : ∀ t, deriv (deriv g) t = g t := by
    intro t
    have h1 : deriv g = fun s => deriv H s - deriv Real.cosh s := by
      ext s; apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cosh.differentiableAt
    have h2 : deriv (deriv g) t = deriv (deriv H) t - deriv (deriv Real.cosh) t := by
      have hH_diff1 : ContDiff ℝ 1 (deriv H) := by
        rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff
        rw [contDiff_succ_iff_deriv] at h_diff
        exact h_diff.2.2
      have hcosh_diff1 : ContDiff ℝ 1 (deriv Real.cosh) := by
        rw [Real.deriv_cosh]; exact Real.contDiff_sinh
      rw [h1]; apply deriv_sub
      · exact hH_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
      · exact hcosh_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    rw [h2, h_ode t, cosh_second_deriv_eq t]
  have hg0 : g 0 = 0 := by simp [g, h_H0, Real.cosh_zero]
  have hg'0 : deriv g 0 = 0 := by
    have h1 : deriv g 0 = deriv H 0 - deriv Real.cosh 0 := by
      apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cosh.differentiableAt
    rw [h1, h_H'0, Real.deriv_cosh, Real.sinh_zero]; ring
  have hg_zero := ode_zero_uniqueness g hg_diff hg_ode hg0 hg'0
  intro t
  have := hg_zero t
  simp only [g] at this; linarith

/-- Hypothesis: Regularity bootstrap for linear ODE. -/
def ode_linear_regularity_bootstrap_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H → Differentiable ℝ H → ContDiff ℝ 2 H

/-- Hypothesis: ODE solutions are continuous. -/
def ode_regularity_continuous_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H

/-- Hypothesis: ODE solutions are differentiable. -/
def ode_regularity_differentiable_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H → Differentiable ℝ H

theorem ode_cosh_uniqueness (H : ℝ → ℝ)
    (h_ODE : ∀ t, deriv (deriv H) t = H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0)
    (h_cont_hyp : ode_regularity_continuous_hypothesis H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis H) :
    ∀ t, H t = Real.cosh t := by
  have h_cont : Continuous H := h_cont_hyp h_ODE
  have h_diff : Differentiable ℝ H := h_diff_hyp h_ODE h_cont
  have h_C2 : ContDiff ℝ 2 H := h_bootstrap_hyp h_ODE h_cont h_diff
  exact ode_cosh_uniqueness_contdiff H h_C2 h_ODE h_H0 h_H'0

/-- Hypothesis: Continuous solutions to d'Alembert are smooth. -/
def dAlembert_continuous_implies_smooth_hypothesis (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) → ContDiff ℝ ⊤ H

/-- Hypothesis: d'Alembert implies ODE everywhere. -/
def dAlembert_to_ODE_hypothesis (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) →
    deriv (deriv H) 0 = 1 → ∀ t, deriv (deriv H) t = H t

theorem dAlembert_cosh_solution
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    (h_deriv2_zero : deriv (deriv H) 0 = 1)
    (h_smooth_hyp : dAlembert_continuous_implies_smooth_hypothesis H)
    (h_ode_hyp : dAlembert_to_ODE_hypothesis H)
    (h_cont_hyp : ode_regularity_continuous_hypothesis H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis H) :
    ∀ t, H t = Real.cosh t := by
  have h_ode : ∀ t, deriv (deriv H) t = H t := h_ode_hyp h_one h_cont h_dAlembert h_deriv2_zero
  have h_even : Function.Even H := dAlembert_even H h_one h_dAlembert
  have h_deriv_zero : deriv H 0 = 0 := by
    have h_smooth := h_smooth_hyp h_one h_cont h_dAlembert
    have h_diff : DifferentiableAt ℝ H 0 := h_smooth.differentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    exact even_deriv_at_zero H h_even h_diff
  exact ode_cosh_uniqueness H h_ode h_one h_deriv_zero h_cont_hyp h_diff_hyp h_bootstrap_hyp

namespace Constructive

/-- Hypothesis: Symmetric second difference limit. -/
def symmetric_second_diff_limit_hypothesis (H : ℝ → ℝ) (t : ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) →
    HasDerivAt (deriv H) 1 0 → Filter.Tendsto (fun u => (H (t+u) + H (t-u) - 2 * H t) / u^2) (nhds 0) (nhds (H t))

end Constructive

end FunctionalEquation
end Cost
end IndisputableMonolith
