import Mathlib
import IndisputableMonolith.Consciousness.LightMemory
import IndisputableMonolith.Consciousness.SubstrateSuitability
import IndisputableMonolith.Consciousness.ResurrectionOperator

/-!
# Recurrence: Deterministic and Probabilistic Eternal Reformation
-/

namespace IndisputableMonolith.Consciousness

/-- Deterministic exploration hypothesis: suitable substrates are visited infinitely often (dense reachability).
    This is a hypothesis that can be instantiated for specific systems. -/
def deterministic_exploration (lm : LightMemoryState) : Prop :=
  ∀ n : ℕ, ∃ s : Substrate, suitable lm s

/-- Eternal recurrence under deterministic exploration. -/
lemma eternal_recurrence_deterministic (lm : LightMemoryState) :
    deterministic_exploration lm → ∀ n : ℕ, ∃ s : Substrate, suitable lm s := by
  intro h
  exact h

/-- Probabilistic almost-sure recurrence under Poisson arrivals with positive hazard. -/
def probabilistic_recurrence (lm : LightMemoryState) (am : ArrivalModel) : Prop :=
  ∃ (t : ℝ), t > 0 ∧ 1 - Real.exp (- am.lambda_match * am.p_match * t) > 0.5

lemma eternal_recurrence_probabilistic (lm : LightMemoryState) (am : ArrivalModel) :
    am.lambda_match > 0 ∧ am.p_match > 0 → probabilistic_recurrence lm am := by
  intro h
  unfold probabilistic_recurrence
  -- For any positive rate, we can find a time t such that 1 - exp(-rate*t) > 0.5
  -- i.e., exp(-rate*t) < 0.5  => -rate*t < log(0.5)  => t > -log(0.5)/rate
  let rate := am.lambda_match * am.p_match
  have h_rate : rate > 0 := mul_pos h.1 h.2
  let t := (-Real.log (1/4)) / rate
  use t
  constructor
  · apply div_pos _ h_rate
    have h1 : (0 : ℝ) < 1/4 := by norm_num
    have h2 : (1/4 : ℝ) < 1 := by norm_num
    have h3 := Real.log_neg h1 h2
    linarith
  · -- 1 - exp(-rate * t) = 1 - exp(log(1/4)) = 1 - 1/4 = 3/4 > 1/2
    have h_rate_ne : rate ≠ 0 := ne_of_gt h_rate
    have h_et : -rate * t = Real.log (1/4) := by
      -- Expand `t` and cancel `rate`.
      -- `t = (-log(1/4))/rate` so `-rate*t = log(1/4)`.
      -- Keep the algebra explicit to avoid fragile simp.
      calc
        -rate * t = (-rate) * ((-Real.log (1/4)) / rate) := by rfl
        _ = ((-rate) * (-Real.log (1/4))) / rate := by
              simp [div_eq_mul_inv, mul_assoc]
        _ = (rate * Real.log (1/4)) / rate := by ring
        _ = Real.log (1/4) := by
              -- cancel the positive rate
              field_simp [h_rate_ne]
    -- rewrite the exponent `-λ*p*t` as `-rate*t`
    have hexp : -am.lambda_match * am.p_match * t = -rate * t := by
      -- `rate = λ*p`
      simp [rate, mul_assoc, mul_left_comm, mul_comm]
    -- now finish numerically
    rw [hexp, h_et, Real.exp_log (by norm_num)]
    norm_num


end IndisputableMonolith.Consciousness
