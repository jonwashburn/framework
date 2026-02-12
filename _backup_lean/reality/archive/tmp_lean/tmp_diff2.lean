import Mathlib

example (a e : ℂ) :
    Complex.normSq (a + e) - Complex.normSq a = Complex.normSq e + 2 * (a * star e).re := by
  have h := Complex.normSq_add a e
  have h' : Complex.normSq (a + e) - Complex.normSq a =
      Complex.normSq e + 2 * (a * (starRingEnd ℂ) e).re := by
    linarith
  simpa using h'
