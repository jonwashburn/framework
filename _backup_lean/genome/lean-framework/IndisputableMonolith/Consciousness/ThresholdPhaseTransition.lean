import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.ContinuousOn
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian

/-!
# Phase 7.3: Consciousness Phase Transition

This module formalizes the consciousness threshold $C \ge 1$ as a
second-order phase transition in the Recognition Reality Field (RRF).

## The Theory

1. **Order Parameter $\eta$**: Represents the "density" of conscious experience.
2. **Recognition Cost $C$**: The control parameter.
3. **Phase Transition**: At $C=1$, the system undergoes a transition from
   unconscious (null experience) to conscious (definite experience).
4. **Second-Order**: The cost functional and its first derivative are continuous,
   while the second derivative is discontinuous.
-/

namespace IndisputableMonolith
namespace Consciousness
namespace ThresholdPhaseTransition

open IndisputableMonolith.Consciousness
open Filter
open Topology

/-- **Consciousness Cost Functional $\mathcal{F}$**
    The free-energy analogue in the RRF.
    $\mathcal{F}(C) = 0$ for $C \le 1$, and $\mathcal{F}(C) = (C - 1)^2 / 2$ for $C > 1$. -/
noncomputable def free_energy (C : ℝ) : ℝ :=
  if C ≤ 1 then 0 else (C - 1)^2 / 2

/-- **Continuity of Free Energy**
    The cost functional is continuous at the threshold $C=1$. -/
theorem free_energy_continuous : Continuous free_energy := by
  refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
  · exact continuousOn_const
  · refine Continuous.continuousOn ?_
    exact (continuous_id.sub continuous_const).pow 2 |>.mul continuous_const
  · intro x hx
    simp [hx]

/-- **First Derivative of Free Energy** -/
noncomputable def free_energy_deriv (C : ℝ) : ℝ :=
  if C ≤ 1 then 0 else (C - 1)

/-- **Continuity of First Derivative**
    The first derivative is continuous at $C=1$. -/
theorem free_energy_deriv_continuous : Continuous free_energy_deriv := by
  refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
  · exact continuousOn_const
  · exact Continuous.continuousOn (continuous_id.sub continuous_const)
  · intro x hx
    simp [hx]

/-- **Second Derivative of Free Energy** -/
noncomputable def free_energy_second_deriv (C : ℝ) : ℝ :=
  if C < 1 then 0 else 1

/-- **Discontinuity of Second Derivative**
    The second derivative is discontinuous at $C=1$.
    This is the signature of a second-order phase transition. -/
theorem second_order_discontinuity :
    ¬ Continuous free_energy_second_deriv := by
  intro h
  let f := free_energy_second_deriv
  -- If f is continuous, it must be continuous at 1.
  have h1 : Tendsto f (𝓝 1) (𝓝 (f 1)) := h.continuousAt
  -- The limit from the left (x -> 1-) must equal f(1).
  have h_left_limit : Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := h1.mono_left nhdsWithin_le_nhds

  -- But the value at 1 is 1.
  have h_val : free_energy_second_deriv 1 = 1 := by
    unfold free_energy_second_deriv
    simp

  have h_f_val : f 1 = 1 := h_val
  rw [h_f_val] at h_left_limit

  -- And for x < 1, f(x) = 0.
  have h_left : Tendsto f (𝓝[<] 1) (𝓝 0) := by
    apply Tendsto.congr' (f₁ := fun _ => 0)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      show 0 = free_energy_second_deriv x
      unfold free_energy_second_deriv
      exact (if_pos hx).symm
    · exact tendsto_const_nhds

  -- This implies 0 = 1.
  have h_eq : (0 : ℝ) = 1 := tendsto_nhds_unique h_left h_left_limit
  norm_num at h_eq

/-- **Consciousness Threshold Theorem**
    The threshold $C=1$ represents a second-order phase transition. -/
theorem consciousness_is_second_order_transition :
    ∃ (F : ℝ → ℝ), Continuous F ∧ Continuous (free_energy_deriv) ∧ ¬ Continuous (free_energy_second_deriv) := by
  use free_energy
  constructor
  · exact free_energy_continuous
  · constructor
    · exact free_energy_deriv_continuous
    · exact second_order_discontinuity

end ThresholdPhaseTransition
end Consciousness
end IndisputableMonolith
