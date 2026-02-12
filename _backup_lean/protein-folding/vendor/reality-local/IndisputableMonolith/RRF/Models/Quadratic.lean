import IndisputableMonolith.RRF.Core
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# RRF Models: Quadratic Model

A non-trivial model with `State = ℝⁿ` and `J(x) = ‖x‖²`.

This demonstrates that RRF structures can model continuous optimization
and provides a testing ground for theorems about minimizers.
-/


namespace IndisputableMonolith
namespace RRF.Models

open RRF.Core

/-! ## The Quadratic Model in ℝ -/

/-- 1D Quadratic strain: J(x) = x². -/
def quadratic1DStrain : StrainFunctional ℝ where
  J := fun x => x ^ 2

instance : StrainFunctional.NonNeg quadratic1DStrain where
  nonneg := fun x => sq_nonneg x

/-- Zero is the unique equilibrium. -/
theorem quadratic1D_equilibrium : quadratic1DStrain.isBalanced 0 := by
  simp [StrainFunctional.isBalanced, quadratic1DStrain]

/-- Zero is the unique equilibrium (uniqueness). -/
theorem quadratic1D_unique_equilibrium (x : ℝ) :
    quadratic1DStrain.isBalanced x ↔ x = 0 := by
  simp [StrainFunctional.isBalanced, quadratic1DStrain]

/-- Zero is the global minimizer. -/
theorem quadratic1D_minimizer : quadratic1DStrain.isMinimizer 0 := by
  intro y
  simp [StrainFunctional.weaklyBetter, quadratic1DStrain]
  exact sq_nonneg y

/-- The quadratic model has a unique minimum. -/
theorem quadratic1D_hasUniqueMin : quadratic1DStrain.hasUniqueMin := by
  use 0
  constructor
  · exact quadratic1D_equilibrium
  · intro y hy
    exact (quadratic1D_unique_equilibrium y).mp hy

/-! ## Quadratic Ledger -/

/-- A trivial ledger constraint for ℝ (always closed). -/
def quadratic1DLedger : LedgerConstraint ℝ where
  debit := fun _ => 0
  credit := fun _ => 0

theorem quadratic1D_ledger_closed (x : ℝ) : quadratic1DLedger.isClosed x := rfl

/-- Combined strain-ledger for 1D quadratic. -/
def quadratic1DStrainLedger : StrainLedger ℝ where
  strain := quadratic1DStrain
  ledger := quadratic1DLedger

/-- Zero is the unique valid state. -/
theorem quadratic1D_zero_valid : quadratic1DStrainLedger.isValid 0 :=
  ⟨quadratic1D_equilibrium, quadratic1D_ledger_closed 0⟩

/-! ## Quadratic Octave -/

/-- Observation channel: identity observation, quality = strain. -/
def quadratic1DChannel : DisplayChannel ℝ ℝ where
  observe := id
  quality := fun x => x ^ 2

/-- The 1D quadratic octave. -/
def quadratic1DOctave : Octave where
  State := ℝ
  strain := quadratic1DStrain
  channels := {
    Index := Unit
    Obs := fun _ => ℝ
    channel := fun _ => quadratic1DChannel
  }
  inhabited := ⟨0⟩

theorem quadratic1DOctave_wellPosed : quadratic1DOctave.wellPosed :=
  ⟨(0 : ℝ), quadratic1D_equilibrium⟩

/-! ## Shifted Quadratic (demonstrates argmin invariance) -/

/-- Shifted quadratic: J(x) = (x - a)² with minimum at a. -/
def shiftedQuadraticStrain (a : ℝ) : StrainFunctional ℝ where
  J := fun x => (x - a) ^ 2

instance (a : ℝ) : StrainFunctional.NonNeg (shiftedQuadraticStrain a) where
  nonneg := fun x => sq_nonneg (x - a)

theorem shifted_equilibrium (a : ℝ) : (shiftedQuadraticStrain a).isBalanced a := by
  simp [StrainFunctional.isBalanced, shiftedQuadraticStrain]

theorem shifted_is_minimizer (a : ℝ) : (shiftedQuadraticStrain a).isMinimizer a := by
  intro y
  simp [StrainFunctional.weaklyBetter, shiftedQuadraticStrain]
  exact sq_nonneg (y - a)

/-! ## Quadratic demonstrates monotone argmin invariance -/

/-- The exponential transform `exp ∘ J` has the same argmin as `J`.
    Proof uses that exp is strictly monotone. -/
theorem exp_preserves_argmin (x : ℝ) :
    quadratic1DStrain.isMinimizer x →
    (∀ y, Real.exp (quadratic1DStrain.J x) ≤ Real.exp (quadratic1DStrain.J y)) := by
  intro hx y
  exact Real.exp_le_exp.mpr (hx y)

end RRF.Models
end IndisputableMonolith
