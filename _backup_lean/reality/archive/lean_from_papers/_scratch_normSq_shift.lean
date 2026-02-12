import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Constants

open Complex
open IndisputableMonolith.LightLanguage.Basis
open IndisputableMonolith.Constants

example (k : ℕ) : Complex.normSq (omega8 ^ k - 1) = 2 - 2 * ((omega8 ^ k).re) := by
  -- Use z*conj z expansion.
  have h : ((omega8 ^ k - 1) * star (omega8 ^ k - 1)) = (Complex.normSq (omega8 ^ k - 1) : ℂ) := by
    simpa using (Complex.mul_conj (omega8 ^ k - 1))
  -- expand LHS
  -- (a-b)*(conj a - conj b) with b=1
  --
  
  -- We'll just compute real part via Complex.add_conj
  --
  sorry
