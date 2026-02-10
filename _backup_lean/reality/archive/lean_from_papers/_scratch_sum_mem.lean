import Mathlib
open scoped BigOperators

def testSum : ℚ :=
  let x : ℚ := 67144 / 10000
  (∑ m ∈ Finset.range 40, x^m / (m.factorial))
