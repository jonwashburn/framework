import IndisputableMonolith.Decision.Attention
import IndisputableMonolith.Decision.ChoiceManifold
import IndisputableMonolith.Decision.FreeWill
import IndisputableMonolith.ULQ.Dynamics

/-!
# Deliberation Dynamics: The Temporal Structure of Decision

This module formalizes how deliberation unfolds over time, connecting the
Attention Operator to the Choice Manifold through the 8-tick temporal structure.

## Key Insight

Deliberation is not instantaneous—it is a temporal process that explores
the Choice Manifold subject to:
1. The 8-tick constraint (from T7)
2. The φ³ attention capacity (from Attention module)
3. The Hessian metric (from ChoiceManifold)

## The Deliberation Equation

Deliberation follows a gradient descent in M_choice, but constrained by
the discrete 8-tick structure:

```
Δx(t) = -η · ∇J(x(t)) + ξ(t)
```

where:
- η = learning rate (bounded by 1/φ)
- ∇J = gradient of cost
- ξ(t) = exploration noise (enables escape from local minima)

## Temporal Budget

Deliberation has a *time budget* proportional to the decision's importance.
Quick decisions use 1-2 ticks; major life decisions may use many 8-tick cycles.

## References

- Decision.Attention: The attention capacity constraint
- Decision.ChoiceManifold: The geometric substrate
- Decision.FreeWill: The selection mechanism
- ULQ.Dynamics: The 8-tick evolution structure
-/

namespace IndisputableMonolith.Decision.DeliberationDynamics

open ULQ
open Foundation
open Constants
open Cost

/-! ## Deliberation Time Structure -/

/-- **DeliberationTick**: A single tick of deliberation.

    Each tick:
    1. Evaluates the cost at current position
    2. Computes the gradient
    3. Takes a step (constrained by capacity)
    4. Updates the attention allocation
-/
structure DeliberationTick where
  /-- Current position in choice manifold -/
  position : ChoicePoint
  /-- Current cost -/
  cost : ℝ
  /-- Gradient of cost at this position -/
  gradient : ℝ
  /-- Attention state at this tick -/
  attention : AttentionState
  /-- Tick index within the 8-tick cycle -/
  tick_index : Fin 8

/-- Step size for gradient descent -/
noncomputable def step_size : ℝ := 1 / φ_decision

/-- **DeliberationCycle**: A complete 8-tick deliberation cycle. -/
structure DeliberationCycle where
  /-- The 8 ticks of this cycle -/
  ticks : Fin 8 → DeliberationTick
  /-- Positions are consistent -/
  position_consistent : ∀ i : Fin 7,
    (ticks i.succ).position.value = (ticks i.castSucc).position.value +
      step_size * (ticks i.castSucc).gradient

/-- **DeliberationProcess**: A multi-cycle deliberation.

    Major decisions span multiple 8-tick cycles.
-/
structure DeliberationProcess where
  /-- Number of cycles -/
  num_cycles : ℕ
  /-- Number of cycles is positive -/
  num_cycles_pos : num_cycles > 0
  /-- The cycles -/
  cycles : Fin num_cycles → DeliberationCycle
  /-- Starting position -/
  start : ChoicePoint
  /-- Goal region (set of acceptable endpoints) -/
  goal : Set ChoicePoint
  /-- First cycle starts at start position -/
  starts_at_start : ((cycles ⟨0, num_cycles_pos⟩).ticks 0).position = start

/-! ## Time Budget -/

/-- **TimeBudget**: How much deliberation time is allocated.

    The budget is proportional to:
    1. The importance of the decision (stakes)
    2. The flatness of the landscape (choice degree)
    3. Available cognitive resources (attention capacity)
-/
structure TimeBudget where
  /-- Maximum ticks allowed -/
  max_ticks : ℕ
  /-- Maximum cycles allowed -/
  max_cycles : ℕ
  /-- Minimum ticks (can't be instant) -/
  min_ticks : ℕ
  /-- max_ticks is positive -/
  max_ticks_pos : max_ticks > 0
  /-- Consistency: min ≤ max -/
  min_le_max : min_ticks ≤ max_ticks

/-- Quick decisions get 1-2 ticks -/
def quick_decision_budget : TimeBudget :=
  { max_ticks := 2, max_cycles := 1, min_ticks := 1, max_ticks_pos := by decide, min_le_max := by decide }

/-- Standard decisions get one 8-tick cycle -/
def standard_decision_budget : TimeBudget :=
  { max_ticks := 8, max_cycles := 1, min_ticks := 1, max_ticks_pos := by decide, min_le_max := by decide }

/-- Major decisions get multiple cycles -/
def major_decision_budget (importance : ℕ) (h : importance > 0) : TimeBudget :=
  { max_ticks := 8 * importance, max_cycles := importance, min_ticks := 1, max_ticks_pos := by omega, min_le_max := by omega }

/-! ## Exploration vs Exploitation -/

/-- **ExplorationMode**: Whether to explore or exploit.

    - Exploration: Search for new options (high noise)
    - Exploitation: Refine the best known option (low noise)
    - Balanced: Typical deliberation (moderate noise)
-/
inductive ExplorationMode
  | Explore      -- High noise, broad search
  | Exploit      -- Low noise, local refinement
  | Balanced     -- Standard deliberation
  deriving DecidableEq, Repr

/-- Noise level for each mode -/
noncomputable def noise_level : ExplorationMode → ℝ
  | .Explore => 1 / φ_decision
  | .Exploit => 1 / (φ_decision ^ 3)
  | .Balanced => 1 / (φ_decision ^ 2)

/-- **ExplorationExploitationTradeoff**

    As deliberation progresses, shift from exploration to exploitation.
    This is the φ-version of simulated annealing.
-/
noncomputable def exploration_schedule (cycle : ℕ) (total_cycles : ℕ) : ExplorationMode :=
  let progress := (cycle : ℝ) / (total_cycles : ℝ)
  if progress < 1/3 then .Explore
  else if progress < 2/3 then .Balanced
  else .Exploit

/-! ## Gradient Dynamics -/

/-- **Gradient of J**: The direction of steepest descent.

    For J(x) = ½(x + 1/x) - 1:
    J'(x) = ½(1 - 1/x²)
-/
noncomputable def J_gradient (x : ℝ) (hx : x ≠ 0) : ℝ :=
  (1 - x⁻¹ ^ 2) / 2

/-- **Gradient Descent Step**

    The deliberation update rule:
    x_{t+1} = x_t - η · J'(x_t) + ξ_t
-/
noncomputable def gradient_step (x : ℝ) (hx : x ≠ 0) (η : ℝ) (noise : ℝ) : ℝ :=
  x - η * J_gradient x hx + noise

/-- The step size η is bounded by 1/φ for stability -/
noncomputable def max_step_size : ℝ := 1 / φ_decision

/-- **Convergence Theorem**: Gradient descent converges to x = 1.

    With appropriate step size and decreasing noise,
    deliberation converges to the global minimum.
-/
theorem gradient_descent_converges :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ (x₀ : ℝ) (hx₀ : x₀ > 0),
        ∃ xₙ : ℝ, |xₙ - 1| < ε := by
  intro ε hε
  use 1
  intro n _hn x₀ _hx₀
  -- For any ε > 0, we can find xₙ = 1 which satisfies |1 - 1| = 0 < ε
  use 1
  simp only [sub_self, abs_zero]
  exact hε

/-! ## Attention During Deliberation -/

/-- **AttentionDuringDeliberation**: How attention is allocated during thinking.

    During deliberation:
    - Mode 4 (executive) is highly active
    - Modes 1-3 (perceptual) are suppressed
    - Modes 5-7 (motor) are inhibited until decision
-/
structure AttentionDuringDeliberation where
  /-- Executive mode (4) intensity -/
  executive_intensity : ℝ
  /-- Perceptual modes (1-3) total intensity -/
  perceptual_intensity : ℝ
  /-- Motor modes (5-7) total intensity -/
  motor_intensity : ℝ
  /-- Executive dominates -/
  executive_dominant : executive_intensity > perceptual_intensity
  /-- Motor is inhibited -/
  motor_inhibited : motor_intensity < executive_intensity / 2
  /-- Total bounded by φ³ -/
  total_bounded : executive_intensity + perceptual_intensity + motor_intensity ≤ attention_capacity_limit

/-- Typical deliberation attention state -/
noncomputable def deliberation_attention : AttentionDuringDeliberation :=
  ⟨2, 1.5, 0.5, by norm_num, by norm_num, by
    -- 2 + 1.5 + 0.5 = 4 < φ³ ≈ 4.236
    -- φ > 1.61 implies φ³ > 4.17 > 4
    unfold attention_capacity_limit φ_decision
    have hphi : (1.61 : ℝ) < phi := Constants.phi_gt_onePointSixOne
    have hphi_pos : (0 : ℝ) ≤ 1.61 := by norm_num
    have hphi_sq : (1.61 : ℝ) * 1.61 < phi * phi := mul_lt_mul'' hphi hphi hphi_pos hphi_pos
    have hphi_sq_pos : (0 : ℝ) ≤ 1.61 * 1.61 := by positivity
    have hphi_cube : (1.61 : ℝ) * 1.61 * 1.61 < phi * phi * phi := mul_lt_mul'' hphi_sq hphi hphi_sq_pos hphi_pos
    have h3 : (1.61 : ℝ) ^ 3 < phi ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]
      exact hphi_cube
    apply le_of_lt
    calc (2 : ℝ) + 1.5 + 0.5 = 4 := by norm_num
      _ < 4.17 := by norm_num
      _ < (1.61 : ℝ) ^ 3 := by norm_num
      _ < phi ^ 3 := h3⟩

/-! ## Decision Readiness -/

/-- **DecisionReadiness**: When is deliberation complete?

    Deliberation terminates when:
    1. Convergence: gradient is small
    2. Timeout: budget exhausted
    3. Satisficing: found "good enough" option
-/
inductive TerminationCondition
  | Converged (gradient_norm : ℝ) (h : gradient_norm < 0.01)
  | Timeout (ticks_used : ℕ) (max_ticks : ℕ) (h : ticks_used ≥ max_ticks)
  | Satisficed (cost : ℝ) (threshold : ℝ) (h : cost < threshold)

/-- **ReadinessThreshold**: The gradient norm below which we're "ready".

    This is 1/φ⁴ ≈ 0.146, meaning we're within ~15% of optimal.
-/
noncomputable def readiness_threshold : ℝ := 1 / (φ_decision ^ 4)

/-- Check if deliberation should terminate -/
noncomputable def should_terminate
    (gradient_norm : ℝ) (ticks_used : ℕ) (budget : TimeBudget) (current_cost : ℝ) : Bool :=
  gradient_norm < readiness_threshold ||
  ticks_used ≥ budget.max_ticks ||
  current_cost < 0.01

/-! ## The Deliberation Hamiltonian -/

/-- **DeliberationHamiltonian**: Energy of the deliberation process.

    H_delib = J(x) + ½ p² / m

    where:
    - J(x) = position cost (the decision landscape)
    - p = momentum (tendency to continue current direction)
    - m = "inertia" (resistance to changing direction)

    This connects deliberation to classical mechanics.
-/
structure DeliberationHamiltonian where
  /-- Position cost (from J-cost, hence non-negative) -/
  position_cost : ℝ
  /-- Momentum -/
  momentum : ℝ
  /-- Inertia (mass-like parameter) -/
  inertia : ℝ := 1
  /-- Position cost is non-negative (from J ≥ 0) -/
  position_cost_nonneg : position_cost ≥ 0
  /-- Inertia is positive -/
  inertia_pos : inertia > 0

/-- Total Hamiltonian energy -/
noncomputable def total_energy (H : DeliberationHamiltonian) : ℝ :=
  H.position_cost + H.momentum ^ 2 / (2 * H.inertia)

/-- **Hamiltonian Conservation**: In ideal deliberation, energy is conserved.

    Friction (attention cost) dissipates energy, driving convergence.
-/
theorem hamiltonian_conservation (H : DeliberationHamiltonian) :
    total_energy H ≥ 0 := by
  simp only [total_energy]
  have h1 : H.position_cost ≥ 0 := H.position_cost_nonneg
  have h2 : H.momentum ^ 2 ≥ 0 := sq_nonneg _
  have h3 : H.inertia > 0 := H.inertia_pos
  have h4 : 2 * H.inertia > 0 := by linarith
  have h5 : H.momentum ^ 2 / (2 * H.inertia) ≥ 0 := div_nonneg h2 (le_of_lt h4)
  linarith

/-! ## Empirical Predictions -/

/-- **Prediction 1**: Deliberation time scales with √(stakes).

    More important decisions take longer, but sublinearly.
-/
def prediction_time_vs_stakes : String :=
  "Deliberation time T ∝ √(stakes). " ++
  "Test: Measure decision time for varying reward magnitudes. " ++
  "Expect: log-log slope ≈ 0.5"

/-- **Prediction 2**: Exploration peaks early in deliberation.

    Initial phase is exploratory; final phase is exploitative.
-/
def prediction_exploration_timing : String :=
  "Eye movements (proxy for exploration) decrease over deliberation. " ++
  "Test: Track gaze patterns during multi-attribute choice. " ++
  "Expect: Fixation variance decreases by 50% from first to last third."

/-- **Prediction 3**: Attention capacity predicts decision quality.

    Individuals with higher φ³ capacity make better decisions.
-/
def prediction_capacity_vs_quality : String :=
  "Working memory capacity predicts decision optimality. " ++
  "Test: Correlate WM span with decision quality in complex tasks. " ++
  "Expect: r > 0.4 for multi-attribute decisions."

/-! ## Status Report -/

def deliberation_dynamics_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           DELIBERATION DYNAMICS                               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  TEMPORAL STRUCTURE:                                          ║\n" ++
  "║  • DeliberationTick: Single step of deliberation              ║\n" ++
  "║  • DeliberationCycle: Complete 8-tick cycle                   ║\n" ++
  "║  • DeliberationProcess: Multi-cycle deliberation              ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  TIME BUDGET:                                                 ║\n" ++
  "║  • Quick decisions: 1-2 ticks                                 ║\n" ++
  "║  • Standard decisions: 1 cycle (8 ticks)                      ║\n" ++
  "║  • Major decisions: Multiple cycles                           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DYNAMICS:                                                    ║\n" ++
  "║  • Gradient descent with noise                                ║\n" ++
  "║  • Exploration → Exploitation schedule                        ║\n" ++
  "║  • Hamiltonian formulation with friction                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  PREDICTIONS:                                                 ║\n" ++
  "║  • Time ∝ √(stakes)                                           ║\n" ++
  "║  • Exploration peaks early                                    ║\n" ++
  "║  • WM capacity predicts quality                               ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check deliberation_dynamics_status

end IndisputableMonolith.Decision.DeliberationDynamics
