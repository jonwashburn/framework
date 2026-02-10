import Mathlib
import IndisputableMonolith.Support.GoldenRatio

/--
`Φ`-scheduler foundations for fusion control. We expose a reusable record for
golden-ratio window tables together with actuator assignments and compliance
predicates. The construction aligns with the φ-timed window requirements in the
fusion patents: ratios between consecutive windows sit in `{φ, φ⁻¹}`, the total
duration equals a declared period, and actuator updates must respect assigned
phase sets with optional jitter tolerances.
-/
namespace IndisputableMonolith
namespace Fusion

open scoped BigOperators
open Classical

noncomputable section

private abbreviation φ : ℝ := Foundation.φ

/-- successor index on `Fin L` with wrap-around. -/
def nextIndex {L : ℕ} (hL : 0 < L) (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, by
    have hmod := Nat.mod_lt (i.val + 1) hL
    simpa using hmod⟩

/-- predicate encoding the φ-ratio constraint between consecutive windows. -/
def PhiRatio (x y : ℝ) : Prop := x = φ * y ∨ x = (1 / φ) * y

lemma PhiRatio_iff_div_mem (x y : ℝ) (hy : y ≠ 0) :
    PhiRatio x y ↔ x / y = φ ∨ x / y = 1 / φ := by
  constructor
  · intro h
    rcases h with hx | hx
    · left
      simp [hx, hy, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    · right
      simp [hx, hy, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · intro h
    rcases h with hx | hx
    · left
      have := congrArg (fun z => z * y) hx
      simpa [hy, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    · right
      have := congrArg (fun z => z * y) hx
      simpa [hy, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this

lemma PhiRatio_pos {x y : ℝ} (h : PhiRatio x y) (hy : 0 < y) : 0 < x := by
  rcases h with hφ | hφ
  · have hpos : 0 < φ := Support.GoldenRatio.phi_pos
    simpa [hφ, mul_comm] using mul_pos hpos hy
  · have hpos : 0 < 1 / φ := Support.GoldenRatio.inv_phi_pos
    simpa [hφ, mul_comm] using mul_pos hpos hy

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
  classical
  have hnonneg : ∀ i : Fin L, 0 ≤ spec.durations i :=
    fun i => (spec.durations_pos i).le
  have hpos : ∃ i : Fin L, 0 < spec.durations i := by
    refine ⟨⟨0, spec.hL⟩, ?_⟩
    simpa using spec.durations_pos ⟨0, spec.hL⟩
  have hsumPos : 0 < ∑ i : Fin L, spec.durations i :=
    Finset.sum_pos fun i _ => hnonneg i
      (by
        rcases hpos with ⟨i, hi⟩
        refine ⟨i, Finset.mem_univ _, hi⟩)
  simpa [spec.period_sum] using hsumPos

/-- Convenience: end time of window `i`. -/
def windowEnd (i : Fin L) : ℝ := spec.starts i + spec.durations i

lemma next_start_eq_windowEnd (i : Fin L) :
    spec.starts (nextIndex spec.hL i) = spec.windowEnd i :=
  spec.start_chain i

lemma start_lt_next_start (i : Fin L) :
    spec.starts i < spec.starts (nextIndex spec.hL i) := by
  have hpos := spec.durations_pos i
  have := add_lt_add_left hpos (spec.starts i)
  simpa [spec.start_chain] using this

end PhiWindowSpec

/-- Assignment-aware φ-scheduler with optional jitter bound. -/
structure PhiScheduler (Actuator : Type _) (L : ℕ)
    extends PhiWindowSpec L where
  assignment : Actuator → Finset (Fin L)
  jitterBound : ℝ
  jitter_nonneg : 0 ≤ jitterBound

namespace PhiScheduler

variable {Actuator : Type _} {L : ℕ} (sched : PhiScheduler Actuator L)

/-- Certificate-style update event. -/
structure Update where
  actuator : Actuator
  window : Fin L
  timestamp : ℝ

@[simp] def allowed (a : Actuator) (w : Fin L) : Prop :=
  w ∈ sched.assignment a

def respectsAssignment (trace : List (Update sched)) : Prop :=
  ∀ e ∈ trace, sched.allowed e.actuator e.window

lemma respectsAssignment_nil :
    sched.respectsAssignment ([] : List (Update sched)) := by
  intro e he
  cases he

lemma respectsAssignment_cons {e : Update sched} {trace : List (Update sched)} :
    sched.respectsAssignment (e :: trace) ↔
      sched.allowed e.actuator e.window ∧ sched.respectsAssignment trace := by
  constructor
  · intro h
    refine And.intro ?left ?right
    · exact h _ (List.mem_cons_self _ _)
    · intro e' he'
      exact h _ (List.mem_cons_of_mem _ he')
  · rintro ⟨hhead, htail⟩ e he
    rcases he with rfl | he'
    · exact hhead
    · exact htail _ he'

def jitterBounded (trace : List (Update sched)) : Prop :=
  ∀ ⦃u v : Update sched⦄,
    (u, v) ∈ trace.zipWith Prod.mk trace.tail →
      |v.timestamp - u.timestamp| ≤ sched.jitterBound

/-- Execution summary used for certificate compatibility proofs. -/
structure Execution where
  phase : ℝ → Fin L
  trace : List (Update sched)
  respects : sched.respectsAssignment trace
  jitter_ok : sched.jitterBounded trace
  periodic : ∀ t, phase (t + sched.period) = phase t
  trace_phase : ∀ e ∈ trace, phase e.timestamp = e.window

end PhiScheduler

end Fusion
end IndisputableMonolith
