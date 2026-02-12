import IndisputableMonolith.Quantum.HilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Observable Algebra for Recognition Science QM Bridge -/

namespace IndisputableMonolith.Quantum

open scoped InnerProductSpace

/-- Self-adjoint operator (observable) -/
structure Observable (HS : RSHilbertSpace) where
  /-- Use the underlying InnerProductSpace instance -/
  [inst : InnerProductSpace ℂ HS.H]
  /-- Bounded linear operator -/
  op : HS.H →L[ℂ] HS.H
  /-- Self-adjoint condition -/
  self_adjoint : ∀ x y : HS.H, ⟪op x, y⟫_ℂ = ⟪x, op y⟫_ℂ

/-- Projection operator -/
structure Projector (HS : RSHilbertSpace) extends Observable HS where
  /-- Idempotent property -/
  idempotent : op.comp op = op

/-- Hamiltonian operator -/
structure Hamiltonian (HS : RSHilbertSpace) extends Observable HS where
  /-- Energy must be bounded below -/
  bounded_below : ∃ E₀ : ℝ, ∀ ψ : NormalizedState HS,
    (⟪op ψ.vec, ψ.vec⟫_ℂ).re ≥ E₀

end IndisputableMonolith.Quantum
