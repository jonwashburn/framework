import Mathlib

namespace IndisputableMonolith
namespace Relativity
namespace Calculus

/-- **LEMMA**: Differentiating the d'Alembert functional equation twice.
    If f(x+y) + f(x-y) = 2f(x)f(y), then f''(x) = f''(0) f(x). -/
theorem dalembert_deriv_ode (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hDA : ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y) :
    ∀ x, deriv (deriv f) x = deriv (deriv f) 0 * f x := by
  intro x
  -- Differentiate w.r.t y twice at y=0
  let g := fun y => f (x + y) + f (x - y)
  let h := fun y => 2 * f x * f y
  have hgh : g = h := by funext y; exact hDA x y

  -- 1. Show that deriv g 0 = 0
  have h_deriv_g : HasDerivAt g 0 0 := by
    -- g'(y) = f'(x+y) - f'(x-y)
    have h1 : HasDerivAt (fun y => f (x + y)) (deriv f x) 0 := by
      have hd : HasDerivAt f (deriv f x) x := hf.differentiable (by decide) |>.differentiableAt.hasDerivAt
      exact hd.comp 0 (hasDerivAt_id 0 |>.const_add x)
    have h2 : HasDerivAt (fun y => f (x - y)) (- deriv f x) 0 := by
      have hd : HasDerivAt f (deriv f x) x := hf.differentiable (by decide) |>.differentiableAt.hasDerivAt
      have hsub : HasDerivAt (fun y => x - y) (-1) 0 := by
        apply HasDerivAt.sub (hasDerivAt_const 0 x) (hasDerivAt_id 0)
      exact hd.comp 0 hsub
    convert h1.add h2 using 1; ring

  -- 2. Show that HasDerivAt (deriv g) (2 * f''(x)) 0
  -- We need to compute the derivative of y => deriv f (x+y) - deriv f (x-y)
  have h_deriv_fun : ∀ y, deriv g y = deriv f (x + y) - deriv f (x - y) := by
    intro y
    have h1 : HasDerivAt (fun s => f (x + s)) (deriv f (x + y)) y := by
      have hd : HasDerivAt f (deriv f (x + y)) (x + y) := hf.differentiable (by decide) |>.differentiableAt.hasDerivAt
      exact hd.comp y (hasDerivAt_id y |>.const_add x)
    have h2 : HasDerivAt (fun s => f (x - s)) (- deriv f (x - y)) y := by
      have hd : HasDerivAt f (deriv f (x - y)) (x - y) := hf.differentiable (by decide) |>.differentiableAt.hasDerivAt
      have hsub : HasDerivAt (fun s => x - s) (-1) y := by
        apply HasDerivAt.sub (hasDerivAt_const y x) (hasDerivAt_id y)
      exact hd.comp y hsub
    exact (h1.add h2).deriv

  have h_second_deriv_g : HasDerivAt (deriv g) (2 * deriv (deriv f) x) 0 := by
    simp_rw [h_deriv_fun]
    -- Differentiate y => deriv f (x+y) - deriv f (x-y)
    have h1 : HasDerivAt (fun y => deriv f (x + y)) (deriv (deriv f) x) 0 := by
      have hd : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
        hf.iterate_deriv 1 1 |>.differentiable (by decide) |>.differentiableAt.hasDerivAt
      exact hd.comp 0 (hasDerivAt_id 0 |>.const_add x)
    have h2 : HasDerivAt (fun y => deriv f (x - y)) (- deriv (deriv f) x) 0 := by
      have hd : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
        hf.iterate_deriv 1 1 |>.differentiable (by decide) |>.differentiableAt.hasDerivAt
      have hsub : HasDerivAt (fun y => x - y) (-1) 0 := by
        apply HasDerivAt.sub (hasDerivAt_const 0 x) (hasDerivAt_id 0)
      exact hd.comp 0 hsub
    convert h1.sub h2 using 1; ring

  -- 3. Show that HasDerivAt (deriv h) (2 * f(x) * f''(0)) 0
  have h_second_deriv_h : HasDerivAt (deriv h) (2 * f x * deriv (deriv f) 0) 0 := by
    unfold h
    have h_deriv_fun : ∀ y, deriv h y = 2 * f x * deriv f y := by
      intro y; rw [deriv_const_mul]; exact hf.differentiable (by decide) |>.differentiableAt
    simp_rw [h_deriv_fun]
    apply HasDerivAt.const_mul
    exact hf.iterate_deriv 1 1 |>.differentiable (by decide) |>.differentiableAt.hasDerivAt

  -- 4. Equate
  have h_eq : deriv (deriv g) 0 = deriv (deriv h) 0 := by rw [hgh]
  rw [h_second_deriv_g.deriv, h_second_deriv_h.deriv] at h_eq
  linarith

end Calculus
end Relativity
end IndisputableMonolith
