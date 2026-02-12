import Mathlib
import IndisputableMonolith.Sonification.Basic

/-!
# Sonification empirics (hypotheses + falsifiers)

This module captures the *empirical* “cross‑octave validation” claim:

> Better structural folds (lower RMSD) have higher audio consonance.

Claim hygiene:
- The core statement is a **Hypothesis** (axiom).
- We also define an explicit **Falsifier** predicate that describes what data
  would refute the hypothesis under a preregistered protocol.

Nothing here “proves nature”; it only fixes the statement shape and the
refutation condition in a machine-checkable way.
-/

namespace IndisputableMonolith.Sonification

/-! ## Data model (EmpiricalAnchor) -/

/-- One paired observation from a preregistered sonification experiment.

Interpretation:
- `rmsd` is a physics-side quality score (lower is better).
- `audioConsonance` is an audio-derived score computed from the MIDI/pitch-bend
  stream **without using RMSD** (otherwise the correlation is tautological). -/
structure FoldObs where
  seed : Nat
  rmsd : ℝ
  audioConsonance : ℝ

/-- Preregistered protocol gate for the “cross-octave” test.

This is intentionally lightweight: it captures the *shape* of the preregistration
without committing to file IO / dataset parsing inside Lean. -/
def PreregisteredDataset (obs : List FoldObs) : Prop :=
  obs.length ≥ 3 ∧
  (∀ o ∈ obs, 0 ≤ o.rmsd) ∧
  (∀ o ∈ obs, 0 ≤ o.audioConsonance)

/-! ## Test predicate + falsifier -/

/-!
### A publishable preregistered statistic: “pairwise violations ≤ k”

Instead of requiring a *perfect* strict ordering (which is brittle under noise),
we define a bounded-violations predicate: among all unordered pairs of seeds,
at most `k` pairs violate the expected monotone relationship.
-/

/-- A pair violates the expected order if lower RMSD does **not** correspond to higher consonance. -/
def ViolatesOrder (o₁ o₂ : FoldObs) : Prop :=
  (o₁.rmsd < o₂.rmsd ∧ o₁.audioConsonance ≤ o₂.audioConsonance) ∨
  (o₂.rmsd < o₁.rmsd ∧ o₂.audioConsonance ≤ o₁.audioConsonance)

/-- Finset of violating unordered index pairs (counted once via `i < j`). -/
noncomputable def violationPairs (obs : List FoldObs) :
    Finset (Fin obs.length × Fin obs.length) := by
  classical
  refine Finset.univ.filter (fun ij =>
    ij.1 < ij.2 ∧
    ViolatesOrder (obs.get ij.1) (obs.get ij.2))

/-- Number of violating unordered pairs. -/
noncomputable def violationCount (obs : List FoldObs) : Nat :=
  (violationPairs obs).card

/-- Bounded-violations form of the cross-octave claim. -/
def CrossOctaveViolationsAtMost (k : Nat) (obs : List FoldObs) : Prop :=
  violationCount obs ≤ k

/-- (Optional) “perfect” form is just the zero-violation special case. -/
def CrossOctaveOrderConsistent (obs : List FoldObs) : Prop :=
  CrossOctaveViolationsAtMost 0 obs

/-- Falsifier: a preregistered dataset with **too many** order violations. -/
def F_TooManyCrossOctaveViolations (k : Nat) (obs : List FoldObs) : Prop :=
  PreregisteredDataset obs ∧ ¬ CrossOctaveViolationsAtMost k obs

/-! ## Hypothesis (the empirical claim) -/

/-- **Hypothesis**: Cross-octave validation holds on the preregistered dataset.

Falsifier hook:
`F_TooManyCrossOctaveViolations k obs` refutes this hypothesis (for that dataset). -/
def H_cross_octave_validation (k : Nat) (obs : List FoldObs) : Prop :=
  PreregisteredDataset obs → CrossOctaveViolationsAtMost k obs

/-! ## Default preregistration (paper-ready) -/

/-- Total number of unordered pairs among `n` observations. -/
def totalPairs (n : Nat) : Nat :=
  n * (n - 1) / 2

/-- Default preregistration: allow at most 10% of unordered pairs to violate the expected order.

Notes:
- This is a **paper-ready** knob: it scales with dataset size.
- For very small datasets (e.g. `n = 3`), this defaults to `0` by floor division. -/
def kDefault (obs : List FoldObs) : Nat :=
  totalPairs obs.length / 10

/-- Paper-ready statement *shape*: the hypothesis instantiated at the default violation budget. -/
def H_cross_octave_validation_default (obs : List FoldObs) : Prop :=
  H_cross_octave_validation (kDefault obs) obs

end IndisputableMonolith.Sonification
