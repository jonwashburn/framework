import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics
import IndisputableMonolith.Thermodynamics.FreeEnergyMonotone
import IndisputableMonolith.Foundation.PhiForcing
import IndisputableMonolith.Cost

/-!
# Memory Ledger: Dynamics of Learning

This module formalizes memory as a **thermodynamic system** governed by Recognition Science
principles. Memory becomes a solvable physics problem: **retention vs. free-energy decay**.

## Proof Status
- `memory_cost_nonneg`: PROVEN ✅
- `emotional_reduces_cost`: PROVEN ✅
- `forgetting_decreases`: PROVEN ✅
- `emotional_forgets_slower`: PROVEN ✅
- `high_temp_maximizes_entropy`: PROVEN ✅
- `low_temp_bistable`: PROVEN ✅
- `learning_rate_nonneg`: PROVEN ✅
- `learning_compounds`: PROVEN ✅

**All thermodynamic memory theorems are now fully proven with no sorries!**
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace MemoryLedger

open Real
open Cost
open Foundation.PhiForcing
open Filter Topology

/-! ## Memory Trace Structure -/

structure LedgerMemoryTrace where
  id : ℕ
  complexity : ℝ
  complexity_pos : 0 < complexity
  emotional_weight : ℝ
  emotional_bounded : 0 ≤ emotional_weight ∧ emotional_weight ≤ 1
  encoding_tick : ℕ
  strength : ℝ
  strength_bounded : 0 ≤ strength ∧ strength ≤ 1
  consolidated : Bool
  ledger_balance : ℤ

noncomputable def base_decay_rate : ℝ := 1 / φ

theorem base_decay_rate_pos : 0 < base_decay_rate := div_pos zero_lt_one phi_pos

def working_memory_window : ℕ := 8
def breath_cycle : ℕ := 1024

theorem breath_cycle_pos : 0 < (breath_cycle : ℝ) := by unfold breath_cycle; norm_num

/-! ## Memory J-Cost -/

noncomputable def memory_cost (trace : LedgerMemoryTrace) (current_tick : ℕ) : ℝ :=
  let time_elapsed := (current_tick - trace.encoding_tick : ℝ)
  let complexity_cost := trace.complexity * Jcost trace.strength
  let time_cost := log (1 + time_elapsed / breath_cycle)
  let interference_cost := Jcost (1 + |trace.ledger_balance| / 10)
  let emotional_discount := 1 - trace.emotional_weight * (1 - 1/φ)
  emotional_discount * (complexity_cost + time_cost + interference_cost)

/-- Emotional discount is always positive (0 < 1 - w*(1 - 1/φ)) -/
lemma emotional_discount_pos (trace : LedgerMemoryTrace) :
    0 < 1 - trace.emotional_weight * (1 - 1/φ) := by
  have h1 : 1 < φ := phi_gt_one
  have h2 : 0 < φ := phi_pos
  have h2' : 0 < 1/φ := div_pos one_pos h2
  have h3 : 1/φ < 1 := by rw [div_lt_one h2]; exact h1
  have h4 : 0 < 1 - 1/φ := by linarith
  have h4' : 1 - 1/φ < 1 := by linarith
  have hw := trace.emotional_bounded
  have h5 : trace.emotional_weight * (1 - 1/φ) < 1 := by
    calc trace.emotional_weight * (1 - 1/φ)
        ≤ 1 * (1 - 1/φ) := mul_le_mul_of_nonneg_right hw.2 (le_of_lt h4)
      _ = 1 - 1/φ := one_mul _
      _ < 1 := h4'
  linarith

theorem memory_cost_nonneg (trace : LedgerMemoryTrace) (t : ℕ)
    (hs : trace.strength > 0) (ht : trace.encoding_tick ≤ t) :
    0 ≤ memory_cost trace t := by
  unfold memory_cost; dsimp only
  apply mul_nonneg (le_of_lt (emotional_discount_pos trace))
  -- Each term is nonnegative: complexity*Jcost ≥ 0, log(1+...) ≥ 0, Jcost(...) ≥ 0
  -- Sum of nonnegatives is nonnegative
  have h1 : 0 ≤ trace.complexity * Jcost trace.strength :=
    mul_nonneg trace.complexity_pos.le (Jcost_nonneg hs)
  have h2 : 0 ≤ log (1 + (↑t - ↑trace.encoding_tick) / ↑breath_cycle) := by
    apply log_nonneg
    have hd : 0 ≤ (↑t - ↑trace.encoding_tick : ℝ) := by simp [sub_nonneg, Nat.cast_le, ht]
    linarith [div_nonneg hd (le_of_lt breath_cycle_pos)]
  have h3 : 0 ≤ Jcost (1 + (↑|trace.ledger_balance| : ℝ) / 10) := by
    apply Jcost_nonneg
    -- |trace.ledger_balance| ≥ 0 as an integer, so its cast to ℝ is also ≥ 0
    have h_abs_nonneg : (0 : ℤ) ≤ |trace.ledger_balance| := abs_nonneg _
    have h_cast_nonneg : (0 : ℝ) ≤ ↑|trace.ledger_balance| := by norm_cast
    linarith [div_nonneg h_cast_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
  -- Sum of nonnegative terms is nonnegative
  exact add_nonneg (add_nonneg h1 h2) h3

/-- Emotional memories have lower cost -/
theorem emotional_reduces_cost (trace1 trace2 : LedgerMemoryTrace) (t : ℕ)
    (h_same : trace1.complexity = trace2.complexity ∧
              trace1.strength = trace2.strength ∧
              trace1.encoding_tick = trace2.encoding_tick ∧
              trace1.ledger_balance = trace2.ledger_balance)
    (h_more : trace1.emotional_weight > trace2.emotional_weight)
    (hs1 : trace1.strength > 0) (_hs2 : trace2.strength > 0)
    (ht : trace1.encoding_tick ≤ t)
    (h_not_perfect : trace1.strength < 1 ∨ t > trace1.encoding_tick ∨ trace1.ledger_balance ≠ 0) :
    memory_cost trace1 t < memory_cost trace2 t := by
  unfold memory_cost; simp only
  -- The base costs are equal since complexity, strength, encoding_tick, ledger_balance are equal
  have h_complexity_eq : trace1.complexity = trace2.complexity := h_same.1
  have h_strength_eq : trace1.strength = trace2.strength := h_same.2.1
  have h_tick_eq : trace1.encoding_tick = trace2.encoding_tick := h_same.2.2.1
  have h_balance_eq : trace1.ledger_balance = trace2.ledger_balance := h_same.2.2.2
  -- Base cost is the same
  have h_base_eq : trace1.complexity * Jcost trace1.strength + log (1 + (↑t - ↑trace1.encoding_tick) / ↑breath_cycle) + Jcost (1 + ↑|trace1.ledger_balance| / 10) =
                   trace2.complexity * Jcost trace2.strength + log (1 + (↑t - ↑trace2.encoding_tick) / ↑breath_cycle) + Jcost (1 + ↑|trace2.ledger_balance| / 10) := by
    rw [h_complexity_eq, h_strength_eq, h_tick_eq, h_balance_eq]
  -- Higher emotional weight means smaller discount factor
  have h1 : 1 < φ := phi_gt_one
  have h2 : 0 < φ := phi_pos
  have h3 : 0 < 1 - 1/φ := by
    have h4 : 1/φ < 1 := by rw [div_lt_one h2]; exact h1
    linarith
  -- discount1 < discount2 because emotional_weight1 > emotional_weight2
  have h_discount_lt : 1 - trace1.emotional_weight * (1 - 1/φ) < 1 - trace2.emotional_weight * (1 - 1/φ) := by
    have h_mul_lt : trace2.emotional_weight * (1 - 1/φ) < trace1.emotional_weight * (1 - 1/φ) :=
      mul_lt_mul_of_pos_right h_more h3
    linarith
  -- Both discounts are positive
  have h_disc1_pos : 0 < 1 - trace1.emotional_weight * (1 - 1/φ) := emotional_discount_pos trace1
  have h_disc2_pos : 0 < 1 - trace2.emotional_weight * (1 - 1/φ) := emotional_discount_pos trace2
  -- Base cost is positive (need at least one component positive)
  have h_jcost_nonneg : 0 ≤ trace1.complexity * Jcost trace1.strength :=
      mul_nonneg trace1.complexity_pos.le (Jcost_nonneg hs1)
  have h_log_nonneg : 0 ≤ log (1 + (↑t - ↑trace1.encoding_tick) / ↑breath_cycle) := by
      apply log_nonneg
    have hd : 0 ≤ (↑t - ↑trace1.encoding_tick : ℝ) := by simp [sub_nonneg, Nat.cast_le, ht]
    linarith [div_nonneg hd (le_of_lt breath_cycle_pos)]
  have h_abs_nonneg : (0 : ℤ) ≤ |trace1.ledger_balance| := abs_nonneg _
  have h_int_nonneg : 0 ≤ Jcost (1 + ↑|trace1.ledger_balance| / 10) := by
    apply Jcost_nonneg
    have h_cast_nonneg : (0 : ℝ) ≤ ↑|trace1.ledger_balance| := by norm_cast
    linarith [div_nonneg h_cast_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
  -- Base cost is positive (at least one of the terms is strictly positive)
  have h_base_pos : 0 < trace1.complexity * Jcost trace1.strength +
                        log (1 + (↑t - ↑trace1.encoding_tick) / ↑breath_cycle) +
                        Jcost (1 + ↑|trace1.ledger_balance| / 10) := by
    rcases h_not_perfect with h_str | h_t | h_bal
    · -- strength < 1 means Jcost > 0 (strength ≠ 1)
      have h_ne_one : trace1.strength ≠ 1 := ne_of_lt h_str
      have h_jcost_pos : 0 < Jcost trace1.strength := Jcost_pos_of_ne_one trace1.strength hs1 h_ne_one
      have h_comp_pos : 0 < trace1.complexity * Jcost trace1.strength :=
        mul_pos trace1.complexity_pos h_jcost_pos
        linarith
    · -- t > encoding_tick means log > 0
      have h_log_pos : 0 < log (1 + (↑t - ↑trace1.encoding_tick) / ↑breath_cycle) := by
        apply log_pos
        have hd : 0 < (↑t - ↑trace1.encoding_tick : ℝ) := by
          simp only [sub_pos, Nat.cast_lt]; exact h_t
        linarith [div_pos hd breath_cycle_pos]
      linarith
    · -- ledger_balance ≠ 0 means interference cost > 0
      have h_bal_pos : (0 : ℤ) < |trace1.ledger_balance| := abs_pos.mpr h_bal
      have h_cast_pos : (0 : ℝ) < ↑|trace1.ledger_balance| := by exact_mod_cast h_bal_pos
      have h_arg_pos : (0 : ℝ) < (1 : ℝ) + (↑|trace1.ledger_balance| : ℝ) / (10 : ℝ) := by
        have hd : (0 : ℝ) < (↑|trace1.ledger_balance| : ℝ) / (10 : ℝ) := div_pos h_cast_pos (by norm_num)
        linarith
      have h_arg_ne_one : (1 : ℝ) + (↑|trace1.ledger_balance| : ℝ) / (10 : ℝ) ≠ (1 : ℝ) := by
        have hd : (0 : ℝ) < (↑|trace1.ledger_balance| : ℝ) / (10 : ℝ) := div_pos h_cast_pos (by norm_num)
        linarith
      have h_int_pos : 0 < Jcost (1 + ↑|trace1.ledger_balance| / 10) :=
        Jcost_pos_of_ne_one _ h_arg_pos h_arg_ne_one
      linarith
  -- Base cost for trace2 is the same (by h_base_eq), so also positive
  have h_base2_pos : 0 < trace2.complexity * Jcost trace2.strength +
                         log (1 + (↑t - ↑trace2.encoding_tick) / ↑breath_cycle) +
                         Jcost (1 + ↑|trace2.ledger_balance| / 10) := by
    rw [← h_base_eq]; exact h_base_pos
  -- Final step: discount1 * base < discount2 * base (since discount1 < discount2 and base > 0)
  -- We need to show: discount1 * base1 < discount2 * base2
  -- Since base1 = base2 (by h_base_eq), we can rewrite and use mul_lt_mul_of_pos_right
  calc (1 - trace1.emotional_weight * (1 - 1 / φ)) *
           (trace1.complexity * Jcost trace1.strength +
            log (1 + (↑t - ↑trace1.encoding_tick) / ↑breath_cycle) +
            Jcost (1 + ↑|trace1.ledger_balance| / 10))
       = (1 - trace1.emotional_weight * (1 - 1 / φ)) *
           (trace2.complexity * Jcost trace2.strength +
            log (1 + (↑t - ↑trace2.encoding_tick) / ↑breath_cycle) +
            Jcost (1 + ↑|trace2.ledger_balance| / 10)) := by rw [h_base_eq]
     _ < (1 - trace2.emotional_weight * (1 - 1 / φ)) *
           (trace2.complexity * Jcost trace2.strength +
            log (1 + (↑t - ↑trace2.encoding_tick) / ↑breath_cycle) +
            Jcost (1 + ↑|trace2.ledger_balance| / 10)) :=
         mul_lt_mul_of_pos_right h_discount_lt h_base2_pos

/-! ## Forgetting Dynamics -/

noncomputable def forgetting_rate (trace : LedgerMemoryTrace) (t : ℕ) : ℝ :=
  base_decay_rate * memory_cost trace t / breath_cycle

noncomputable def apply_forgetting (trace : LedgerMemoryTrace) (n_cycles : ℕ) (current_tick : ℕ) : ℝ :=
  let rate := forgetting_rate trace current_tick
  trace.strength * exp (-rate * n_cycles * working_memory_window)

theorem forgetting_decreases (trace : LedgerMemoryTrace) (n m : ℕ) (t : ℕ)
    (h : n ≤ m) (hs : trace.strength > 0) (ht : trace.encoding_tick ≤ t) :
    apply_forgetting trace m t ≤ apply_forgetting trace n t := by
  unfold apply_forgetting forgetting_rate
  have h_mcost : 0 ≤ memory_cost trace t := memory_cost_nonneg trace t hs ht
  have h_rate : 0 ≤ base_decay_rate * memory_cost trace t / breath_cycle :=
    div_nonneg (mul_nonneg base_decay_rate_pos.le h_mcost) breath_cycle_pos.le
  apply mul_le_mul_of_nonneg_left _ trace.strength_bounded.1
  rw [exp_le_exp]
  have h_nm : (n : ℝ) ≤ (m : ℝ) := by norm_cast
  have h_window : 0 < (working_memory_window : ℝ) := by norm_num [working_memory_window]
  nlinarith [mul_nonneg h_rate (le_of_lt h_window)]

/-- Emotional memories forget slower -/
theorem emotional_forgets_slower (trace1 trace2 : LedgerMemoryTrace) (n t : ℕ)
    (h_same : trace1.complexity = trace2.complexity ∧
              trace1.strength = trace2.strength ∧
              trace1.encoding_tick = trace2.encoding_tick ∧
              trace1.ledger_balance = trace2.ledger_balance)
    (h_more : trace1.emotional_weight > trace2.emotional_weight)
    (hs1 : trace1.strength > 0) (hs2 : trace2.strength > 0)
    (ht1 : trace1.encoding_tick ≤ t) (ht2 : trace2.encoding_tick ≤ t)
    (h_not_perfect : trace1.strength < 1 ∨ t > trace1.encoding_tick ∨ trace1.ledger_balance ≠ 0)
    (hn : n > 0) :
    apply_forgetting trace1 n t > apply_forgetting trace2 n t := by
  unfold apply_forgetting forgetting_rate
  -- trace1.strength = trace2.strength by h_same
  have h_strength_eq : trace1.strength = trace2.strength := h_same.2.1
  -- Lower cost => lower rate => smaller negative exponent => larger exp result
  have h_cost_lt : memory_cost trace1 t < memory_cost trace2 t :=
    emotional_reduces_cost trace1 trace2 t h_same h_more hs1 hs2 ht1 h_not_perfect
  -- Rates: rate = base_decay_rate * cost / breath_cycle
  have h_base_pos : 0 < base_decay_rate := base_decay_rate_pos
  have h_breath_pos : 0 < (breath_cycle : ℝ) := breath_cycle_pos
  have h_rate_lt : base_decay_rate * memory_cost trace1 t / breath_cycle <
                   base_decay_rate * memory_cost trace2 t / breath_cycle := by
    apply div_lt_div_of_pos_right _ h_breath_pos
    apply mul_lt_mul_of_pos_left h_cost_lt h_base_pos
  -- Negative exponents: -rate1 * n * window > -rate2 * n * window (since rate1 < rate2)
  have h_window_pos : 0 < (working_memory_window : ℝ) := by norm_num [working_memory_window]
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_exp_arg_lt : -(base_decay_rate * memory_cost trace1 t / breath_cycle * n * working_memory_window) >
                      -(base_decay_rate * memory_cost trace2 t / breath_cycle * n * working_memory_window) := by
    simp only [neg_lt_neg_iff]
    apply mul_lt_mul_of_pos_right _ h_window_pos
    apply mul_lt_mul_of_pos_right h_rate_lt hn_pos
  -- exp is strictly increasing, so larger argument means larger result
  have h_exp_lt : exp (-(base_decay_rate * memory_cost trace1 t / breath_cycle * n * working_memory_window)) >
                  exp (-(base_decay_rate * memory_cost trace2 t / breath_cycle * n * working_memory_window)) :=
    exp_lt_exp.mpr h_exp_arg_lt
  -- Finally, multiply by equal positive strengths
  have hs_pos : 0 < trace1.strength := hs1
  rw [h_strength_eq] at hs_pos
  -- Need to show: str1 * exp(-rate1 * n * w) > str2 * exp(-rate2 * n * w)
  -- Since str1 = str2 and exp(-rate1*n*w) > exp(-rate2*n*w)
  have h_goal1 : trace1.strength * exp (-(base_decay_rate * memory_cost trace1 t / ↑breath_cycle) * ↑n * ↑working_memory_window)
               = trace2.strength * exp (-(base_decay_rate * memory_cost trace1 t / ↑breath_cycle) * ↑n * ↑working_memory_window) := by
    rw [h_strength_eq]
  have h_goal2 : trace2.strength * exp (-(base_decay_rate * memory_cost trace1 t / ↑breath_cycle) * ↑n * ↑working_memory_window)
               > trace2.strength * exp (-(base_decay_rate * memory_cost trace2 t / ↑breath_cycle) * ↑n * ↑working_memory_window) := by
    apply mul_lt_mul_of_pos_left _ hs_pos
    -- Both exponents are the same as h_exp_lt after simplification
    have heq1 : -(base_decay_rate * memory_cost trace1 t / ↑breath_cycle) * ↑n * ↑working_memory_window
              = -(base_decay_rate * memory_cost trace1 t / ↑breath_cycle * ↑n * ↑working_memory_window) := by ring
    have heq2 : -(base_decay_rate * memory_cost trace2 t / ↑breath_cycle) * ↑n * ↑working_memory_window
              = -(base_decay_rate * memory_cost trace2 t / ↑breath_cycle * ↑n * ↑working_memory_window) := by ring
    rw [heq1, heq2]
    exact h_exp_lt
  linarith [h_goal1, h_goal2]

/-! ## Thermodynamic Limits -/

noncomputable def equilibrium_remember_prob (sys : RecognitionSystem) (trace : LedgerMemoryTrace) (t : ℕ) : ℝ :=
  let J := memory_cost trace t
  exp (-J / sys.TR) / (exp (-J / sys.TR) + 1)

/-- At high temperature, p → 0.5 -/
theorem high_temp_maximizes_entropy (trace : LedgerMemoryTrace) (t : ℕ) :
    ∀ (ε : ℝ), ε > 0 → ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR > T₀ →
      |equilibrium_remember_prob sys trace t - 0.5| < ε := by
  intro ε hε
  -- Let J = memory_cost trace t (some fixed real number)
  set J := memory_cost trace t with hJ_def
  -- Choose T₀ large enough that -J/T is small
  -- We need |exp(-J/T) - 1| < 2ε to ensure |p - 0.5| < ε
  -- Using the bound: |exp(x) - 1| ≤ |x| * exp(|x|) for small |x|
  -- For T > |J|/(ε), we have |J/T| < ε, giving roughly |exp(-J/T) - 1| < ε*e^ε < 2ε
  --
  -- Simpler approach: use that |p - 0.5| = |e-1|/(2(e+1)) ≤ |e-1|/2
  -- and |exp(x) - 1| → 0 as x → 0.
  --
  -- Take T₀ = max(1, |J|/ε + |J| + 1) to ensure |-J/T| < ε and well-behaved bounds
  use max 1 ((|J| + 1) * (1/ε + 1))
  constructor
  · apply lt_max_of_lt_left; norm_num
  · intro sys hT
    have hT_pos : 0 < sys.TR := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _) |>.trans hT
    unfold equilibrium_remember_prob; simp only
    -- Let e = exp(-J/sys.TR)
    set e := exp (-J / sys.TR) with he_def
    have he_pos : 0 < e := exp_pos _
    have h_denom_pos : 0 < e + 1 := by linarith
    -- The key identity: p - 0.5 = (e - 1) / (2(e+1))
    have h_05_eq : (0.5 : ℝ) = 1 / 2 := by norm_num
    rw [h_05_eq]
    have h_diff : e / (e + 1) - (1 : ℝ) / 2 = (e - 1) / (2 * (e + 1)) := by
      field_simp
      ring
    rw [h_diff]
    -- |p - 0.5| = |e - 1| / (2(e+1)) ≤ |e - 1| / 2 (since e+1 ≥ 1)
    have h_abs_bound : |e - 1| / (2 * (e + 1)) ≤ |e - 1| / 2 := by
      apply div_le_div_of_nonneg_left (abs_nonneg _)
      · norm_num
      · have h1 : 1 ≤ e + 1 := by linarith [he_pos]
        linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_div, abs_of_pos (by linarith : 0 < 2 * (e + 1))]
    apply lt_of_le_of_lt h_abs_bound
    -- Now we need |e - 1| / 2 < ε, i.e., |e - 1| < 2ε
    -- Use Real.abs_exp_sub_one_le: if |x| ≤ 1, then |exp(x) - 1| ≤ 2 * |x|
    have h_goal_equiv : |e - 1| / 2 < ε ↔ |e - 1| < 2 * ε := by
      constructor
      · intro h; have := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp h; linarith
      · intro h; rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
    rw [h_goal_equiv]
    -- Need |e - 1| < 2 * ε
    -- We have T > (|J|+1)*(1/ε+1), so |J|/T < ε when ε ≤ 1
    -- For the exp bound, we need |-J/T| ≤ 1
    have h_T_bound : sys.TR > (|J| + 1) * (1 / ε + 1) := lt_of_le_of_lt (le_max_right _ _) hT
    have h_J_over_T : |J| / sys.TR < ε := by
      have h1 : (|J| + 1) * (1 / ε + 1) > |J| / ε := by
        have hε_pos : 0 < ε := hε
        have h_pos : 0 < 1/ε + 1 := by linarith [one_div_pos.mpr hε_pos]
        calc (|J| + 1) * (1 / ε + 1) = |J|/ε + |J| + 1/ε + 1 := by ring
           _ > |J|/ε := by linarith [abs_nonneg J, one_div_pos.mpr hε_pos]
      have h2 : sys.TR > |J| / ε := lt_trans h1 h_T_bound
      have hT_pos' : 0 < sys.TR := hT_pos
      rwa [div_lt_iff₀ hT_pos', mul_comm, ← div_lt_iff₀ hε]
    -- Now check if |-J/T| ≤ 1 (needed for the exp bound)
    have h_abs_small : |-J / sys.TR| ≤ 1 := by
      have h_abs_TR : |sys.TR| = sys.TR := abs_of_pos hT_pos
      rw [abs_div, abs_neg, h_abs_TR]
      -- |J|/T ≤ 1 follows from T > |J| + 1
      have h_one_le : 1 ≤ 1/ε + 1 := by linarith [one_div_pos.mpr hε]
      have h1 : sys.TR > |J| + 1 := by
        calc sys.TR > (|J| + 1) * (1/ε + 1) := h_T_bound
           _ ≥ (|J| + 1) * 1 := mul_le_mul_of_nonneg_left h_one_le (by linarith [abs_nonneg J])
           _ = |J| + 1 := mul_one _
      have h2 : |J| / sys.TR < 1 := by
        rw [div_lt_one (α := ℝ) hT_pos]
        linarith
      linarith
    -- Apply the exponential bound
    have h_exp_bound : |e - 1| ≤ 2 * |-J / sys.TR| := by
      rw [he_def]
      exact Real.abs_exp_sub_one_le h_abs_small
    have h_abs_TR : |sys.TR| = sys.TR := abs_of_pos hT_pos
    calc |e - 1| ≤ 2 * |-J / sys.TR| := h_exp_bound
       _ = 2 * (|J| / sys.TR) := by rw [abs_div, abs_neg, h_abs_TR]
       _ < 2 * ε := by linarith [mul_lt_mul_of_pos_left h_J_over_T (by norm_num : (0 : ℝ) < 2)]

/-- At low temperature with J > 0, p → 0 -/
theorem low_temp_bistable (trace : LedgerMemoryTrace) (t : ℕ)
    (hs : trace.strength > 0) (ht : trace.encoding_tick ≤ t)
    (h_not_perfect : trace.strength < 1 ∨ t > trace.encoding_tick ∨ trace.ledger_balance ≠ 0) :
    ∀ (ε : ℝ), ε > 0 → ∃ T₀ > 0, ∀ sys : RecognitionSystem, sys.TR < T₀ →
      equilibrium_remember_prob sys trace t < ε ∨
      equilibrium_remember_prob sys trace t > 1 - ε := by
  intro ε hε
  set J := memory_cost trace t with hJ_def
  -- Under h_not_perfect, J > 0 (base cost is positive)
  have hJ_pos : 0 < J := by
    rw [hJ_def]; unfold memory_cost
    have h_disc_pos : 0 < 1 - trace.emotional_weight * (1 - 1/φ) := emotional_discount_pos trace
    apply mul_pos h_disc_pos
    -- Base cost is positive when h_not_perfect holds
    have h_jcost_nonneg : 0 ≤ trace.complexity * Jcost trace.strength :=
      mul_nonneg trace.complexity_pos.le (Jcost_nonneg hs)
    have h_log_nonneg : 0 ≤ log (1 + (↑t - ↑trace.encoding_tick) / ↑breath_cycle) := by
      apply log_nonneg
      have hd : 0 ≤ (↑t - ↑trace.encoding_tick : ℝ) := by simp [sub_nonneg, Nat.cast_le, ht]
      linarith [div_nonneg hd (le_of_lt breath_cycle_pos)]
    have h_abs_nonneg : (0 : ℤ) ≤ |trace.ledger_balance| := abs_nonneg _
    have h_int_nonneg : 0 ≤ Jcost (1 + ↑|trace.ledger_balance| / 10) := by
      apply Jcost_nonneg
      have h_cast_nonneg : (0 : ℝ) ≤ ↑|trace.ledger_balance| := by norm_cast
      linarith [div_nonneg h_cast_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    rcases h_not_perfect with h_str | h_t | h_bal
    · have h_ne_one : trace.strength ≠ 1 := ne_of_lt h_str
      have h_jcost_pos : 0 < Jcost trace.strength := Jcost_pos_of_ne_one trace.strength hs h_ne_one
      have h_comp_pos : 0 < trace.complexity * Jcost trace.strength :=
        mul_pos trace.complexity_pos h_jcost_pos
      linarith
    · have h_log_pos : 0 < log (1 + (↑t - ↑trace.encoding_tick) / ↑breath_cycle) := by
        apply log_pos
        have hd : 0 < (↑t - ↑trace.encoding_tick : ℝ) := by
          simp only [sub_pos, Nat.cast_lt]; exact h_t
        linarith [div_pos hd breath_cycle_pos]
      linarith
    · have h_bal_pos : (0 : ℤ) < |trace.ledger_balance| := abs_pos.mpr h_bal
      have h_cast_pos : (0 : ℝ) < ↑|trace.ledger_balance| := by exact_mod_cast h_bal_pos
      have h_arg_pos : (0 : ℝ) < (1 : ℝ) + (↑|trace.ledger_balance| : ℝ) / (10 : ℝ) := by
        have hd : (0 : ℝ) < (↑|trace.ledger_balance| : ℝ) / (10 : ℝ) := div_pos h_cast_pos (by norm_num)
        linarith
      have h_arg_ne_one : (1 : ℝ) + (↑|trace.ledger_balance| : ℝ) / (10 : ℝ) ≠ (1 : ℝ) := by
        have hd : (0 : ℝ) < (↑|trace.ledger_balance| : ℝ) / (10 : ℝ) := div_pos h_cast_pos (by norm_num)
        linarith
      have h_int_pos : 0 < Jcost (1 + ↑|trace.ledger_balance| / 10) :=
        Jcost_pos_of_ne_one _ h_arg_pos h_arg_ne_one
      linarith
  -- Choose T₀ small enough: for J > 0, exp(-J/T) → 0 as T → 0+
  -- We need p = e/(e+1) < ε where e = exp(-J/T) → 0
  -- For e < ε/(1-ε) (assuming ε < 1), we have p < ε
  -- exp(-J/T) < ε/(1-ε) when -J/T < log(ε/(1-ε)), i.e., T < J/(-log(ε/(1-ε)))
  -- For ε ≥ 1, just take T small enough that e < 1
  use min 1 (J / (|log (ε / 2)| + 1))
  constructor
  · apply lt_min_iff.mpr
    constructor
    · norm_num
    · apply div_pos hJ_pos
      linarith [abs_nonneg (log (ε / 2))]
  · intro sys hT
    have hT_pos : 0 < sys.TR := sys.TR_pos
    left -- We'll show p < ε (since J > 0)
    unfold equilibrium_remember_prob; simp only
    set e := exp (-J / sys.TR) with he_def
    have he_pos : 0 < e := exp_pos _
    have h_denom_pos : 0 < e + 1 := by linarith
    -- p = e/(e+1), and e is very small for small T
    -- Need: e/(e+1) < ε
    -- Since e/(e+1) < e (for e > 0), it suffices to show e < ε
    have h_p_lt_e : e / (e + 1) < e := by
      rw [div_lt_iff₀ h_denom_pos]
      -- Need: e < e * (e + 1) = e*e + e  ⟺  0 < e*e (since e > 0)
      have h1 : e * (e + 1) = e * e + e := by ring
      rw [h1]
      have h2 : 0 < e * e := mul_pos he_pos he_pos
      linarith
    apply lt_of_lt_of_le h_p_lt_e
    -- Need e ≤ ε, i.e., exp(-J/T) ≤ ε
    -- -J/T < log ε when T < J/(-log ε) (for ε < 1)
    -- Our bound T < J/(|log(ε/2)|+1) ensures exp(-J/T) is small
    -- For now, use the structure: with small T and J > 0, exp(-J/T) → 0
    have hT_small : sys.TR < J / (|log (ε / 2)| + 1) :=
      lt_of_lt_of_le hT (min_le_right _ _)
    have h_arg_large : -J / sys.TR < log ε := by
      have h_denom_pos' : 0 < |log (ε / 2)| + 1 := by linarith [abs_nonneg (log (ε / 2))]
      have h1 : J / (|log (ε / 2)| + 1) > 0 := div_pos hJ_pos h_denom_pos'
      have h2 : sys.TR > 0 := hT_pos
      -- -J/T < log ε  ⟺  -log ε < J/T (after neg_lt)
      rw [neg_div, neg_lt]
      -- Now goal is: -log ε < J / sys.TR
      -- Case split on whether ε ≥ 1
      by_cases hε1 : 1 ≤ ε
      · -- If ε ≥ 1, then log ε ≥ 0, so -log ε ≤ 0 < J/T
        have h_log_nonneg : 0 ≤ log ε := log_nonneg hε1
        have h_neg_log_le : -log ε ≤ 0 := neg_nonpos.mpr h_log_nonneg
        have h_div_pos : 0 < J / sys.TR := div_pos hJ_pos h2
        linarith
      · -- If ε < 1, we have -log ε > 0, but J/T > |log(ε/2)| + 1 > |log ε|
        push_neg at hε1
        have h_log_neg : log ε < 0 := log_neg hε hε1
        -- From hT_small: T < J / (|log(ε/2)| + 1), so J/T > |log(ε/2)| + 1
        have h_J_div_T : J / sys.TR > |log (ε / 2)| + 1 := by
          have h3 : sys.TR * (|log (ε / 2)| + 1) < J := by
            calc sys.TR * (|log (ε / 2)| + 1) < (J / (|log (ε / 2)| + 1)) * (|log (ε / 2)| + 1) := by
                   apply mul_lt_mul_of_pos_right hT_small h_denom_pos'
               _ = J := div_mul_cancel₀ J (ne_of_gt h_denom_pos')
          -- (|log (ε / 2)| + 1) * sys.TR < J ⟺ |log (ε / 2)| + 1 < J / sys.TR
          have h4 : (|log (ε / 2)| + 1) * sys.TR < J := by linarith [mul_comm sys.TR (|log (ε / 2)| + 1)]
          exact (lt_div_iff₀ h2).mpr h4
        -- Now show |log(ε/2)| ≥ |log ε|, i.e., -log(ε/2) ≥ -log ε
        have h_half_pos : 0 < ε / 2 := by linarith
        have h_half_lt_one : ε / 2 < 1 := by linarith
        have h_log_half_neg : log (ε / 2) < 0 := log_neg h_half_pos h_half_lt_one
        have h_half_lt_eps : ε / 2 < ε := by linarith
        have h_log_mono : log (ε / 2) < log ε := log_lt_log h_half_pos h_half_lt_eps
        -- |log(ε/2)| = -log(ε/2) > -log ε = |log ε|
        have h_abs_compare : |log (ε / 2)| > |log ε| := by
          rw [abs_of_neg h_log_half_neg, abs_of_neg h_log_neg]
          linarith
        -- -log ε = |log ε| < |log(ε/2)| < |log(ε/2)| + 1 < J/T
        have h_neg_log : -log ε = |log ε| := by rw [abs_of_neg h_log_neg]
        linarith
    have h_exp_bound : e ≤ ε := by
      rw [he_def]
      have h1 : exp (-J / sys.TR) < exp (log ε) := exp_lt_exp.mpr h_arg_large
      have h2 : exp (log ε) = ε := exp_log hε
      linarith [h1, h2]
    exact h_exp_bound

/-! ## Learning and Consolidation -/

structure LearningEvent where
  experience : LedgerMemoryTrace
  attention : ℝ
  attention_bounded : 0 ≤ attention ∧ attention ≤ 1
  repetitions : ℕ
  spacing : ℕ

noncomputable def spaced_bonus (event : LearningEvent) : ℝ :=
  log (1 + event.spacing / working_memory_window) / log φ

theorem spaced_bonus_nonneg (event : LearningEvent) : 0 ≤ spaced_bonus event := by
  unfold spaced_bonus
  apply div_nonneg
  · apply log_nonneg
    have hs : 0 ≤ (event.spacing : ℝ) := by norm_cast; omega
    have hw : 0 < (working_memory_window : ℝ) := by norm_num [working_memory_window]
    linarith [div_nonneg hs hw.le]
  · exact log_nonneg Constants.phi_ge_one

noncomputable def learning_rate (event : LearningEvent) : ℝ :=
  φ ^ (-(event.repetitions : ℝ)) * event.attention * (1 + spaced_bonus event)

theorem learning_rate_nonneg (event : LearningEvent) : 0 ≤ learning_rate event := by
  unfold learning_rate
  apply mul_nonneg
  · apply mul_nonneg (rpow_pos_of_pos phi_pos _).le event.attention_bounded.1
  · linarith [spaced_bonus_nonneg event]

theorem learning_compounds (e1 e2 : LearningEvent)
    (h_same : e1.experience = e2.experience)
    (h_more : e1.repetitions > e2.repetitions)
    (h_attn : e1.attention = e2.attention)
    (h_space : e1.spacing = e2.spacing)
    (hs1 : e1.experience.strength > 0) (_hs2 : e2.experience.strength > 0) :
    let dr1 := -learning_rate e1 * memory_cost e1.experience e1.experience.encoding_tick
    let dr2 := -learning_rate e2 * memory_cost e2.experience e2.experience.encoding_tick
    dr1 ≥ dr2 := by
  intro dr1 dr2
  have h_pow_le : φ ^ (-(e1.repetitions : ℝ)) ≤ φ ^ (-(e2.repetitions : ℝ)) := by
    apply rpow_le_rpow_of_exponent_le (le_of_lt phi_gt_one)
    simp only [neg_le_neg_iff, Nat.cast_le]; exact Nat.le_of_lt h_more
  have h_bonus : spaced_bonus e1 = spaced_bonus e2 := by unfold spaced_bonus; rw [h_space]
  have h_lr_le : learning_rate e1 ≤ learning_rate e2 := by
    unfold learning_rate; rw [h_attn, h_bonus]
    apply mul_le_mul_of_nonneg_right _ (by linarith [spaced_bonus_nonneg e2])
    apply mul_le_mul_of_nonneg_right h_pow_le e2.attention_bounded.1
  have h_cost_same : memory_cost e1.experience e1.experience.encoding_tick =
                     memory_cost e2.experience e2.experience.encoding_tick := by rw [h_same]
  have h_cost_nonneg : 0 ≤ memory_cost e1.experience e1.experience.encoding_tick :=
    memory_cost_nonneg _ _ hs1 (le_refl _)
  simp only [dr1, dr2]; rw [h_cost_same]; nlinarith

def memory_ledger_status : List (String × String) :=
  [ ("memory_cost_nonneg", "PROVEN")
  , ("emotional_reduces_cost", "PROVEN")
  , ("forgetting_decreases", "PROVEN")
  , ("emotional_forgets_slower", "PROVEN")
  , ("high_temp_maximizes_entropy", "PROVEN")
  , ("low_temp_bistable", "PROVEN")
  , ("learning_rate_nonneg", "PROVEN")
  , ("learning_compounds", "PROVEN")
  ]

#eval memory_ledger_status

end MemoryLedger
end Thermodynamics
end IndisputableMonolith
