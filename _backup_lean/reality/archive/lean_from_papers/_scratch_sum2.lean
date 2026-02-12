import Mathlib
open scoped BigOperators

example : True := by
  let s : Finset ℕ := ({1,2,3} : Finset ℕ)
  let f : ℕ → ℕ := fun x => x
  have h : f 1 ≤ ∑ x ∈ s, f x := by
    simpa using (Finset.single_le_sum (s:=s) (f:=f)
      (by intro i hi; exact Nat.zero_le _) (by decide : (1:ℕ) ∈ s))
  trivial
