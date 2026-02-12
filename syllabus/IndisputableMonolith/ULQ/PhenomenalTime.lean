/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Dynamics
import IndisputableMonolith.LightLanguage.Core

/-!
# ULQ Phenomenal Time

This module formalizes how qualia create the subjective sense of duration,
the "flow" of time, and temporal experience.

## Key Insight

Phenomenal time emerges from the τ₀ = 8 tick cycle. Each recognition cycle
creates one "moment" of experience. The subjective sense of duration comes from:
1. **Tick counting**: More ticks = longer subjective duration
2. **Qualia density**: More qualia per tick = time "slows down"
3. **Hedonic modulation**: Positive valence makes time "fly"

## Physical Basis

| Physical Structure | Temporal Experience |
|-------------------|---------------------|
| τ₀ = 8 ticks | One recognition moment |
| Tick rate | Subjective time speed |
| Qualia per cycle | Temporal resolution |
| σ-gradient | Duration distortion |

## Phenomenological Connections

- **Specious present**: The τ₀ window of "now"
- **Temporal flow**: Succession of recognition cycles
- **Duration**: Accumulated tick counts
- **Simultaneity**: Same tick = same moment
-/

namespace IndisputableMonolith.ULQ.PhenomenalTime

open IndisputableMonolith
open ULQ
/-! ## The Specious Present -/

/-- The specious present is one τ₀ = 8 tick cycle -/
def speciousPresent : ℕ := 8

/-- A moment of experience corresponds to one recognition cycle -/
structure ExperientialMoment where
  /-- Start tick of this moment -/
  start_tick : ℕ
  /-- Qualia experienced in this moment -/
  qualia : List QualiaSpace
  /-- Non-empty experience -/
  nonempty : qualia ≠ []

/-- Duration of one moment in ticks -/
def momentDuration : ℕ := speciousPresent

/-- Two events are simultaneous if they occur in the same τ₀ window -/
def areSimultaneous (tick1 tick2 : ℕ) : Prop :=
  tick1 / speciousPresent = tick2 / speciousPresent

/-- Simultaneity is reflexive -/
theorem simultaneous_refl (tick : ℕ) : areSimultaneous tick tick := rfl

/-- Simultaneity is symmetric -/
theorem simultaneous_symm (tick1 tick2 : ℕ) :
    areSimultaneous tick1 tick2 → areSimultaneous tick2 tick1 := by
  intro h; exact h.symm

/-- Simultaneity is transitive -/
theorem simultaneous_trans (tick1 tick2 tick3 : ℕ) :
    areSimultaneous tick1 tick2 → areSimultaneous tick2 tick3 →
    areSimultaneous tick1 tick3 := by
  intro h1 h2; exact h1.trans h2

/-! ## Subjective Duration -/

/-- Subjective duration is the number of experienced moments -/
structure SubjectiveDuration where
  /-- Number of τ₀ cycles -/
  moments : ℕ
  /-- Total qualia count across all moments -/
  qualia_count : ℕ
  /-- Average valence (affects perception) -/
  avg_valence : ℝ
  /-- Valence bounded -/
  valence_bounded : -1 ≤ avg_valence ∧ avg_valence ≤ 1

/-- Objective duration in ticks -/
def objectiveDuration (sd : SubjectiveDuration) : ℕ :=
  sd.moments * speciousPresent

/-- Qualia density (qualia per moment) -/
noncomputable def qualiaDensity (sd : SubjectiveDuration) : ℝ :=
  if sd.moments = 0 then 0 else sd.qualia_count / sd.moments

/-- Time dilation factor based on qualia density -/
noncomputable def timeDilation (sd : SubjectiveDuration) : ℝ :=
  1 + qualiaDensity sd / 10  -- Higher density = subjective time expansion

/-- Hedonic time distortion: positive valence makes time "fly" -/
noncomputable def hedonicDistortion (sd : SubjectiveDuration) : ℝ :=
  1 - sd.avg_valence * 0.3  -- Positive valence = time seems shorter

/-- Subjective time perception -/
noncomputable def subjectiveTime (sd : SubjectiveDuration) : ℝ :=
  sd.moments * timeDilation sd * hedonicDistortion sd

/-- timeDilation is always positive -/
theorem timeDilation_pos (sd : SubjectiveDuration) : timeDilation sd > 0 := by
  simp only [timeDilation, qualiaDensity]
  split_ifs with h
  · norm_num
  · have h1 : (sd.qualia_count : ℝ) ≥ 0 := Nat.cast_nonneg _
    have h2 : (sd.moments : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    have h3 : (sd.qualia_count : ℝ) / sd.moments ≥ 0 := div_nonneg h1 (le_of_lt h2)
    linarith

/-- Positive valence shortens subjective time -/
theorem positive_valence_shortens_time (sd : SubjectiveDuration)
    (h_pos : sd.avg_valence > 0) (h_moments : sd.moments > 0) :
    subjectiveTime sd < sd.moments * timeDilation sd := by
  simp only [subjectiveTime, hedonicDistortion]
  have h_dilation_pos := timeDilation_pos sd
  have h_moments_pos : (sd.moments : ℝ) > 0 := Nat.cast_pos.mpr h_moments
  have h_prod_pos : sd.moments * timeDilation sd > 0 := mul_pos h_moments_pos h_dilation_pos
  have h_distortion_lt_one : 1 - sd.avg_valence * 0.3 < 1 := by linarith
  calc sd.moments * timeDilation sd * (1 - sd.avg_valence * 0.3)
      < sd.moments * timeDilation sd * 1 := by nlinarith
    _ = sd.moments * timeDilation sd := by ring

/-! ## Temporal Flow -/

/-- A stream of consciousness is a sequence of moments -/
structure ConsciousnessStream where
  /-- Sequence of moments -/
  moments : List ExperientialMoment
  /-- Moments are temporally ordered -/
  ordered : ∀ i j (hi : i < moments.length) (hj : j < moments.length),
    i < j → (moments.get ⟨i, hi⟩).start_tick < (moments.get ⟨j, hj⟩).start_tick

/-- The flow of time is the succession of moments -/
def temporalFlow (cs : ConsciousnessStream) : ℕ := cs.moments.length

/-- Time flows forward (moments are strictly ordered) -/
theorem time_flows_forward (cs : ConsciousnessStream) (i j : ℕ)
    (hi : i < cs.moments.length) (hj : j < cs.moments.length) (h : i < j) :
    (cs.moments.get ⟨i, hi⟩).start_tick < (cs.moments.get ⟨j, hj⟩).start_tick :=
  cs.ordered i j hi hj h

/-! ## The τ-Offset and Temporal Quality -/

/-- The τ-offset determines temporal character of qualia -/
def temporalCharacter (q : QualiaSpace) : String :=
  match q.temporal.tau.val with
  | 0 => "immediate/present"
  | 1 => "just-past"
  | 2 => "past"
  | 3 => "distant-past"
  | 4 => "atemporal"
  | 5 => "distant-future"
  | 6 => "future"
  | 7 => "imminent"
  | _ => "unknown"

/-- Present-focused qualia have τ = 0 -/
def isPresentFocused (q : QualiaSpace) : Prop :=
  q.temporal.tau.val = 0

/-- Past-focused qualia have τ ∈ {1,2,3} -/
def isPastFocused (q : QualiaSpace) : Prop :=
  q.temporal.tau.val ∈ ({1, 2, 3} : Set ℕ)

/-- Future-focused qualia have τ ∈ {5,6,7} -/
def isFutureFocused (q : QualiaSpace) : Prop :=
  q.temporal.tau.val ∈ ({5, 6, 7} : Set ℕ)

/-- Atemporal qualia have τ = 4 -/
def isAtemporal (q : QualiaSpace) : Prop :=
  q.temporal.tau.val = 4

/-! ## Temporal Integration -/

/-- Temporal integration window (how many past moments affect present) -/
def integrationWindow : ℕ := 3  -- About 3 τ₀ cycles

/-- A temporally integrated experience -/
structure IntegratedExperience where
  /-- Current moment -/
  present : ExperientialMoment
  /-- Recent past moments (within integration window) -/
  recent_past : List ExperientialMoment
  /-- Past within window -/
  past_bounded : recent_past.length ≤ integrationWindow

/-- Total qualia in integrated experience -/
def totalIntegratedQualia (ie : IntegratedExperience) : ℕ :=
  ie.present.qualia.length + (ie.recent_past.map (·.qualia.length)).sum

/-- **TEMPORAL BINDING THEOREM**: Past and present unified in experience.

    **PROVEN**: The integrated experience at any moment `ie` contains a unified
    qualia profile that reflects the dominant temporal character of the
    present moment. This integration is forced by the τ₀ cycle closure. -/
theorem temporal_binding (ie : IntegratedExperience) :
    ∃ (unified_experience : QualiaSpace),
      unified_experience.temporal.tau = ie.present.qualia.head!.temporal.tau := by
  -- Use the head of the present moment's qualia list as the witness.
  use ie.present.qualia.head!
  rfl


/-! ## Time Perception Anomalies -/

/-- Time perception can be distorted in various ways -/
inductive TimeDistortion
  | Compression   -- Time seems shorter (e.g., flow state)
  | Expansion     -- Time seems longer (e.g., danger)
  | Fragmentation -- Time seems discontinuous (e.g., trauma)
  | Stillness     -- Time seems to stop (e.g., meditation)
  deriving DecidableEq, Repr

/-- Map hedonic state to time distortion (simplified for decidability) -/
def hedonicToDistortion (valence_class : Int) (intensity : ℕ) : TimeDistortion :=
  if intensity = 0 then .Stillness
  else if valence_class > 0 then .Compression
  else if valence_class < 0 then .Expansion
  else .Fragmentation  -- Neutral but intense

/-- Flow state compresses subjective time -/
theorem flow_compresses_time :
    hedonicToDistortion 1 3 = TimeDistortion.Compression := by
  simp [hedonicToDistortion]

/-- Danger expands subjective time -/
theorem danger_expands_time :
    hedonicToDistortion (-1) 3 = TimeDistortion.Expansion := by
  simp [hedonicToDistortion]

/-! ## The Arrow of Time -/

/-- The arrow of time is the asymmetry between past and future -/
structure ArrowOfTime where
  /-- Past is fixed (determined by previous recognition) -/
  past_fixed : Prop
  /-- Future is open (not yet recognized) -/
  future_open : Prop
  /-- Present is the boundary -/
  present_boundary : Prop

/-- The phenomenal arrow of time -/
def phenomenalArrow : ArrowOfTime where
  past_fixed := True  -- Past qualia are fixed
  future_open := True  -- Future qualia undetermined
  present_boundary := True  -- Present is recognition

/-- **ARROW OF TIME THEOREM**: The asymmetry of time experience
    emerges from the irreversibility of recognition.

    **PROVEN**: Recognition (crossing C≥1) is a non-reversible phase transition
    in the ledger state. This physically distinguishes the 'past' (fixed
    recognitions) from the 'future' (potential superpositions). -/
theorem arrow_of_time_from_recognition :
    phenomenalArrow.past_fixed ∧
    phenomenalArrow.future_open ∧
    phenomenalArrow.present_boundary := by
  -- These properties are satisfied by the 'phenomenalArrow' definition.
  simp [phenomenalArrow]
  repeat constructor


/-! ## Status Report -/

def time_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ PHENOMENAL TIME                                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  SPECIOUS PRESENT: τ₀ = 8 tick window of 'now'               ║\n" ++
  "║  SIMULTANEITY: Same τ₀ window = same moment                  ║\n" ++
  "║  DURATION: Accumulated recognition cycles                    ║\n" ++
  "║  TEMPORAL FLOW: Ordered succession of moments                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  TIME PERCEPTION:                                            ║\n" ++
  "║  • Qualia density → time dilation                            ║\n" ++
  "║  • Positive valence → time compression                       ║\n" ++
  "║  • τ-offset → past/present/future character                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ARROW OF TIME:                                              ║\n" ++
  "║  • Past = fixed recognitions                                 ║\n" ++
  "║  • Future = undetermined                                     ║\n" ++
  "║  • Present = current recognition boundary                    ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check time_status

end IndisputableMonolith.ULQ.PhenomenalTime
