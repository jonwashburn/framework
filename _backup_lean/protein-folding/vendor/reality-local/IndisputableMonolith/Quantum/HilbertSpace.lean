import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection

/-! # Hilbert Space for Recognition Science QM Bridge -/

namespace IndisputableMonolith.Quantum

/-- A separable Hilbert space with finite or countable dimension -/
structure RSHilbertSpace where
  /-- The underlying vector space -/
  H : Type*
  /-- Inner product space instance -/
  [innerProduct : InnerProductSpace ℂ H]
  /-- Completeness (Hilbert) -/
  [complete : CompleteSpace H]
  /-- Separability (countable dense subset) -/
  [separable : SeparableSpace H]
  /-- Inhabited (at least one state) -/
  [nonempty : Nonempty H]

/-- State vector in the Hilbert space -/
abbrev State (HS : RSHilbertSpace) := HS.H

/-- Normalized state (unit vector) -/
structure NormalizedState (HS : RSHilbertSpace) where
  vec : HS.H
  norm_one : ‖vec‖ = 1

end IndisputableMonolith.Quantum
