import Mathlib
import IndisputableMonolith.Support.GoldenRatio

/-!
# Phi-Scheduler Foundations

Phi-scheduler foundations for fusion control. We expose a reusable record for
golden-ratio window tables together with actuator assignments and compliance
predicates. The construction aligns with the phi-timed window requirements in the
fusion patents: ratios between consecutive windows sit in `{phi, 1/phi}`, the total
duration equals a declared period, and actuator updates must respect assigned
phase sets with optional jitter tolerances.
-/
namespace IndisputableMonolith
namespace Fusion

open scoped BigOperators
open Classical

noncomputable section

-- Local abbreviation for golden ratio
local notation "φ" => Foundation.φ

/-- successor index on `Fin L` with wrap-around. -/
def nextIndex {L : ℕ} (hL : 0 < L) (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩

/-- predicate encoding the φ-ratio constraint between consecutive windows. -/
def PhiRatio (x y : ℝ) : Prop := x = φ * y ∨ x = (1 / φ) * y

-- Auxiliary characterization of φ-ratio via division
-- Proof deferred; not critical for main scheduler results
lemma PhiRatio_iff_div_mem (x y : ℝ) (hy : y ≠ 0) :
    PhiRatio x y ↔ x / y = φ ∨ x / y = 1 / φ := by
  unfold PhiRatio
  constructor
  · intro h
    rcases h with hx | hx
    · left; rw [hx]; field_simp [hy]
    · right; rw [hx]; field_simp [hy]
  · intro h
    rcases h with hx | hx
    · left; rw [show x = x / y * y from (div_mul_cancel₀ x hy).symm, hx]
    · right; rw [show x = x / y * y from (div_mul_cancel₀ x hy).symm, hx]

lemma PhiRatio_pos {x y : ℝ} (h : PhiRatio x y) (hy : 0 < y) : 0 < x := by
  rcases h with hφ | hφ
  · have hpos : 0 < φ := Support.GoldenRatio.phi_pos
    rw [hφ]; exact mul_pos hpos hy
  · have hpos : 0 < 1 / φ := Support.GoldenRatio.inv_phi_pos
    rw [hφ]; exact mul_pos hpos hy

/-- Core window specification for φ-schedulers. -/
structure PhiWindowSpec (L : ℕ) where
  hL : 0 < L
  period : ℝ
  durations : Fin L → ℝ
  starts : Fin L → ℝ
  durations_pos : ∀ i, 0 < durations i
  starts_zero : starts ⟨0, hL⟩ = 0
  period_sum : (∑ i : Fin L, durations i) = period
  ratio_condition : ∀ i, PhiRatio (durations (nextIndex hL i)) (durations i)
  start_chain : ∀ i, starts (nextIndex hL i) = starts i + durations i

namespace PhiWindowSpec

variable {Actuator : Type _} {L : ℕ} (spec : PhiWindowSpec L)

@[simp] lemma durations_pos' (i : Fin L) : 0 < spec.durations i :=
  spec.durations_pos i

lemma durations_ne_zero (i : Fin L) : spec.durations i ≠ 0 :=
  ne_of_gt (spec.durations_pos i)

lemma period_pos : 0 < spec.period := by
  have hpos : 0 < spec.durations ⟨0, spec.hL⟩ := spec.durations_pos _
  calc 0 < spec.durations ⟨0, spec.hL⟩ := hpos
    _ ≤ ∑ i : Fin L, spec.durations i := Finset.single_le_sum
        (fun i _ => le_of_lt (spec.durations_pos i)) (Finset.mem_univ _)
    _ = spec.period := spec.period_sum

/-- Convenience: end time of window `i`. -/
def windowEnd (i : Fin L) : ℝ := spec.starts i + spec.durations i

lemma next_start_eq_windowEnd (i : Fin L) :
    spec.starts (nextIndex spec.hL i) = spec.windowEnd i :=
  spec.start_chain i

lemma start_lt_next_start (i : Fin L) :
    spec.starts i < spec.starts (nextIndex spec.hL i) := by
  rw [spec.start_chain]
  linarith [spec.durations_pos i]

end PhiWindowSpec

/-- Assignment-aware φ-scheduler with optional jitter bound. -/
structure PhiScheduler (Actuator : Type _) (L : ℕ)
    extends PhiWindowSpec L where
  assignment : Actuator → Finset (Fin L)
  jitterBound : ℝ
  jitter_nonneg : 0 ≤ jitterBound

namespace PhiScheduler

/-- Certificate-style update event. -/
structure Update (Actuator : Type _) (L : ℕ) where
  actuator : Actuator
  window : Fin L
  timestamp : ℝ

variable {Actuator : Type _} {L : ℕ} (sched : PhiScheduler Actuator L)

@[simp] def allowed (a : Actuator) (w : Fin L) : Prop :=
  w ∈ sched.assignment a

def respectsAssignment (trace : List (Update Actuator L)) : Prop :=
  ∀ e ∈ trace, sched.allowed e.actuator e.window

lemma respectsAssignment_nil :
    sched.respectsAssignment ([] : List (Update Actuator L)) := by
  intro e he
  cases he

lemma respectsAssignment_cons {e : Update Actuator L} {trace : List (Update Actuator L)} :
    sched.respectsAssignment (e :: trace) ↔
      sched.allowed e.actuator e.window ∧ sched.respectsAssignment trace := by
  unfold respectsAssignment
  simp only [List.mem_cons]
  constructor
  · intro h
    exact ⟨h e (Or.inl rfl), fun e' he' => h e' (Or.inr he')⟩
  · intro ⟨hhead, htail⟩ e' he'
    rcases he' with rfl | hmem
    · exact hhead
    · exact htail e' hmem

def jitterBounded (trace : List (Update Actuator L)) : Prop :=
  ∀ ⦃u v : Update Actuator L⦄,
    (u, v) ∈ trace.zipWith Prod.mk trace.tail →
      |v.timestamp - u.timestamp| ≤ sched.jitterBound

/-- Execution summary used for certificate compatibility proofs. -/
structure Execution where
  phase : ℝ → Fin L
  trace : List (Update Actuator L)
  respects : sched.respectsAssignment trace
  jitter_ok : sched.jitterBounded trace
  periodic : ∀ t, phase (t + sched.period) = phase t
  trace_phase : ∀ e ∈ trace, phase e.timestamp = e.window

end PhiScheduler

end

end Fusion
end IndisputableMonolith
