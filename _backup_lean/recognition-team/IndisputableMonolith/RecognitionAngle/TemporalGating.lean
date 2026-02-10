import Mathlib
import IndisputableMonolith.Measurement.RecognitionAngle.ActionSmallAngle

/-!
# Temporal Gating: Eight‑Tick Windows and Feasibility Predicate

Abstracts the discrete sampling/gating windows (eight‑tick) and defines a feasibility
predicate combining the angular threshold with temporal admissibility.
-/

noncomputable section

namespace IndisputableMonolith
namespace Measurement
namespace RecognitionAngle

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Coprime moduli framing for double-period phasing (e.g., 8 and 45). -/
structure PhaseParams where
  modA : ℕ := 8
  modB : ℕ := 45
  coprime : Nat.Coprime modA modB := by decide

/-- Parameters for eight‑tick gating: a chosen phase and a nonempty set of admissible windows. -/
structure EightTickParams where
  phase  : Fin 8
  window : Set (Fin 8)
  hNonempty : window.Nonempty

/-- Temporal admissibility for a tick index `n`. -/
def timeOK (n : ℤ) (p : EightTickParams) : Prop :=
  let cls : Fin 8 := (Int.toNat (Int.emod n 8)).toFin
  cls ∈ p.window

/-- Geometric admissibility (angle threshold). -/
def angleOK (x y z : R3) (Amax : ℝ) : Prop :=
  angleAt x y z ≥ thetaMin Amax

/-- Combined feasibility for event index `n`. -/
def feasible (x y z : R3) (Amax : ℝ) (p : EightTickParams) (n : ℤ) : Prop :=
  angleOK x y z Amax ∧ timeOK n p

/-! ## Basic feasibility theorems (parameterized) -/

/-- If the geometric threshold fails, no event index is feasible (for any gating params). -/
theorem no_feasible_if_angle_below_threshold
    {x y z : R3} {Amax : ℝ} (hθlt : angleAt x y z < thetaMin Amax)
    (p : EightTickParams) : ∀ n : ℤ, ¬ feasible x y z Amax p n := by
  intro n h
  have : angleAt x y z ≥ thetaMin Amax := h.left
  exact (not_le.mpr hθlt) this

/-- If a geometric threshold holds and there exists a permitted time slot,
then a feasible event exists. -/
theorem exists_feasible_if_angleOK_and_time_slot
    {x y z : R3} {Amax : ℝ} {p : EightTickParams}
    (hθ : angleOK x y z Amax) (hslot : ∃ n : ℤ, timeOK n p) :
    ∃ n : ℤ, feasible x y z Amax p n := by
  rcases hslot with ⟨n, hn⟩
  exact ⟨n, And.intro hθ hn⟩

/-- Example: with a trivial always-on window, any angle-OK configuration is feasible. -/
def trivialParams : EightTickParams :=
  { phase := 0, window := Set.univ, hNonempty := by classical exact Set.nonempty_univ }

example {x y z : R3} {Amax : ℝ} (hθ : angleOK x y z Amax) :
    ∃ n : ℤ, feasible x y z Amax trivialParams n := by
  refine exists_feasible_if_angleOK_and_time_slot (x := x) (y := y) (z := z) (Amax := Amax)
    (p := trivialParams) hθ ?_
  exact ⟨(0 : ℤ), by simp [timeOK, trivialParams]⟩

end RecognitionAngle
end Measurement
end IndisputableMonolith
