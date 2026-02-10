/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Experience
import IndisputableMonolith.ULQ.Dynamics
import IndisputableMonolith.Constants

/-!
# ULQ Altered States of Consciousness

This module models non-ordinary states of consciousness within the ULQ framework.
Each altered state is characterized by specific parameter regimes:

## State Classifications

1. **Meditation**: σ → 0 (hedonic equilibration)
2. **Psychedelics**: Mode mixing (DFT boundary dissolution)
3. **Dreams**: Reduced C threshold (easier experience actualization)
4. **Anesthesia**: C < 1 (below consciousness threshold)
5. **Flow States**: Optimal Θ-coherence + moderate C

## Key Insight

Altered states are not mysterious — they are specific parameter regimes
of the same ULQ machinery that produces ordinary consciousness.
The mathematical structure predicts HOW to achieve each state.
-/

namespace IndisputableMonolith.ULQ.AlteredStates

open IndisputableMonolith
open ULQ
open Constants

/-! ## State Parameters -/

/-- Parameters characterizing a consciousness state -/
structure StateParameters where
  /-- Recognition cost (consciousness threshold parameter) -/
  recognition_cost : ℝ
  /-- Hedonic skew (σ value) -/
  sigma : ℝ
  /-- Mode mixing coefficient (0 = pure mode, 1 = full mixing) -/
  mode_mixing : ℝ
  /-- Θ-coherence (phase synchronization) -/
  theta_coherence : ℝ
  /-- Parameters bounded -/
  cost_nonneg : recognition_cost ≥ 0
  mixing_bounded : 0 ≤ mode_mixing ∧ mode_mixing ≤ 1
  coherence_bounded : 0 ≤ theta_coherence ∧ theta_coherence ≤ 1

/-- Ordinary waking consciousness parameters -/
noncomputable def ordinaryWaking : StateParameters where
  recognition_cost := 1.5  -- Above threshold
  sigma := 0.1            -- Slight positive bias
  mode_mixing := 0.1      -- Mostly pure modes
  theta_coherence := 0.7  -- Good binding
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-! ## Meditation States -/

/-- **MEDITATION**: Characterized by σ → 0 (hedonic neutrality).

    Deep meditation approaches the hedonic optimum where σ = 0.
    This is the state of equanimity described across contemplative traditions. -/
structure MeditationState where
  /-- Base parameters -/
  params : StateParameters
  /-- σ is near zero -/
  sigma_near_zero : |params.sigma| < 0.1
  /-- Coherence is high -/
  high_coherence : params.theta_coherence > 0.8

/-- Deep meditation parameters -/
noncomputable def deepMeditation : StateParameters where
  recognition_cost := 1.2  -- Above threshold but calm
  sigma := 0.01           -- Near-zero hedonic skew
  mode_mixing := 0.05     -- Very pure modes (clarity)
  theta_coherence := 0.95 -- Very high binding
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-- **PREDICTION**: Meditation → σ approaches zero.

    Experienced meditators should show:
    1. Reduced hedonic reactivity (σ → 0)
    2. Increased phase coherence (better binding)
    3. Reduced mode mixing (clearer qualia) -/
def meditation_prediction : String :=
  "MEDITATION STATE:\n" ++
  "• σ → 0 (hedonic equilibrium, equanimity)\n" ++
  "• Θ-coherence ↑ (enhanced unity of consciousness)\n" ++
  "• Mode mixing ↓ (clearer, purer qualia)\n" ++
  "• C stable above threshold (sustained awareness)"

/-! ## Psychedelic States -/

/-- **PSYCHEDELICS**: Characterized by mode mixing (DFT boundary dissolution).

    Psychedelics increase mode mixing, causing qualia to blend in
    unusual ways (synesthesia, ego dissolution). -/
structure PsychedelicState where
  /-- Base parameters -/
  params : StateParameters
  /-- High mode mixing -/
  high_mixing : params.mode_mixing > 0.5
  /-- Variable coherence -/
  variable_coherence : True  -- Θ can fluctuate wildly

/-- Peak psychedelic state parameters -/
noncomputable def peakPsychedelic : StateParameters where
  recognition_cost := 2.0  -- Often heightened
  sigma := 0.3            -- Can be positive (mystical) or negative (challenging)
  mode_mixing := 0.8      -- High mixing (synesthesia)
  theta_coherence := 0.4  -- Reduced binding (ego dissolution)
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-- **PREDICTION**: Psychedelics → increased mode mixing.

    Under psychedelics:
    1. Mode boundaries dissolve (synesthesia)
    2. Θ-coherence decreases (ego dissolution)
    3. C often increases (intensified experience)
    4. σ becomes volatile (emotional lability) -/
def psychedelic_prediction : String :=
  "PSYCHEDELIC STATE:\n" ++
  "• Mode mixing ↑↑ (synesthesia, unusual qualia combinations)\n" ++
  "• Θ-coherence ↓ (ego dissolution, boundary loss)\n" ++
  "• C often ↑ (intensified, overwhelming experience)\n" ++
  "• σ volatile (rapid hedonic swings)"

/-! ## Dream States -/

/-- **DREAMS**: Characterized by reduced C threshold.

    During REM sleep, the threshold for experience actualization is lower,
    allowing weaker signals to become conscious experiences. -/
structure DreamState where
  /-- Base parameters -/
  params : StateParameters
  /-- Reduced threshold (below normal waking) -/
  reduced_threshold : params.recognition_cost < 1.0
  /-- Still above minimum for any experience -/
  above_minimum : params.recognition_cost > 0.3

/-- REM dream state parameters -/
noncomputable def remDream : StateParameters where
  recognition_cost := 0.6  -- Below normal threshold
  sigma := 0.0            -- Variable, dream-dependent
  mode_mixing := 0.3      -- Some mixing (surreal content)
  theta_coherence := 0.5  -- Moderate binding (fragmented narrative)
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-- **PREDICTION**: Dreams → reduced C threshold.

    During dreaming:
    1. C threshold lowered (weak signals become conscious)
    2. Mode mixing moderate (surreal combinations)
    3. Θ-coherence reduced (fragmented narrative)
    4. σ follows dream content (emotional dreams) -/
def dream_prediction : String :=
  "DREAM STATE:\n" ++
  "• C threshold ↓ (weak signals actualize as experience)\n" ++
  "• Mode mixing moderate (surreal but somewhat coherent)\n" ++
  "• Θ-coherence ↓ (narrative fragmentation)\n" ++
  "• σ content-dependent (emotional valence varies)"

/-! ## Anesthesia States -/

/-- **ANESTHESIA**: Characterized by C < 1 (below consciousness threshold).

    General anesthesia pushes C below the experience threshold,
    preventing qualia from actualizing despite neural activity. -/
structure AnesthesiaState where
  /-- Base parameters -/
  params : StateParameters
  /-- Below consciousness threshold -/
  below_threshold : params.recognition_cost < 1.0
  /-- Coherence disrupted -/
  low_coherence : params.theta_coherence < 0.3

/-- General anesthesia parameters -/
noncomputable def generalAnesthesia : StateParameters where
  recognition_cost := 0.3  -- Well below threshold
  sigma := 0.0            -- No hedonic experience
  mode_mixing := 0.0      -- No mode activity
  theta_coherence := 0.1  -- Coherence disrupted
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-- **PREDICTION**: Anesthesia → C < 1.

    Under anesthesia:
    1. C pushed below 1 (no conscious experience)
    2. Θ-coherence disrupted (no binding possible)
    3. All modes suppressed (no qualia actualize)
    4. σ irrelevant (no hedonic experience) -/
def anesthesia_prediction : String :=
  "ANESTHESIA STATE:\n" ++
  "• C < 1 (below experience threshold)\n" ++
  "• Θ-coherence disrupted (binding impossible)\n" ++
  "• All modes suppressed (no qualia)\n" ++
  "• σ = 0 (no hedonic experience)"

/-! ## Flow States -/

/-- **FLOW**: Characterized by optimal Θ-coherence and moderate C.

    Flow states occur when coherence is high but not maximal,
    and C is sufficient for clear experience but not overwhelming. -/
structure FlowState where
  /-- Base parameters -/
  params : StateParameters
  /-- Optimal coherence (high but not maximal) -/
  optimal_coherence : 0.7 < params.theta_coherence ∧ params.theta_coherence < 0.9
  /-- Moderate C (above threshold, not overwhelming) -/
  optimal_cost : 1.0 < params.recognition_cost ∧ params.recognition_cost < 2.0
  /-- Low mode mixing (focused attention) -/
  focused : params.mode_mixing < 0.2

/-- Flow state parameters -/
noncomputable def flowState : StateParameters where
  recognition_cost := 1.3  -- Above threshold, not overwhelming
  sigma := 0.2            -- Slight positive (enjoyment)
  mode_mixing := 0.1      -- Focused, pure modes
  theta_coherence := 0.85 -- High but not maximal
  cost_nonneg := by norm_num
  mixing_bounded := by constructor <;> norm_num
  coherence_bounded := by constructor <;> norm_num

/-- **PREDICTION**: Flow → optimal parameter balance.

    In flow states:
    1. C in optimal range (clear but not overwhelming)
    2. Θ-coherence high (strong binding, unified action)
    3. Mode mixing low (focused attention)
    4. σ slightly positive (engagement, enjoyment) -/
def flow_prediction : String :=
  "FLOW STATE:\n" ++
  "• C in optimal range (clear, not overwhelming)\n" ++
  "• Θ-coherence high (unified experience-action)\n" ++
  "• Mode mixing low (focused attention)\n" ++
  "• σ slightly positive (engagement, enjoyment)"

/-! ## State Transitions -/

/-- Transition between states requires parameter shifts -/
structure StateTransition where
  /-- Starting state -/
  from_state : StateParameters
  /-- Ending state -/
  to_state : StateParameters
  /-- Time for transition (in eight-tick units) -/
  duration : ℕ

/-- Waking → Meditation transition -/
noncomputable def wakingToMeditation : StateTransition where
  from_state := ordinaryWaking
  to_state := deepMeditation
  duration := 100  -- ~100 eight-tick cycles

/-- Waking → Sleep transition -/
noncomputable def wakingToSleep : StateTransition where
  from_state := ordinaryWaking
  to_state := remDream
  duration := 500  -- Longer transition

/-! ## Status Report -/

def alteredstates_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ ALTERED STATES                                 ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MEDITATION: σ → 0, Θ ↑, mixing ↓                           ║\n" ++
  "║  PSYCHEDELICS: mixing ↑↑, Θ ↓, C ↑                          ║\n" ++
  "║  DREAMS: C threshold ↓, mixing moderate                      ║\n" ++
  "║  ANESTHESIA: C < 1, Θ disrupted                             ║\n" ++
  "║  FLOW: C optimal, Θ high, mixing ↓                          ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  Each state = specific ULQ parameter regime.                ║\n" ++
  "║  Transitions = parameter trajectories.                       ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check alteredstates_status

end IndisputableMonolith.ULQ.AlteredStates
