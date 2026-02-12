import Mathlib
open scoped BigOperators
#check (by
  let s : Finset Nat := {1,2,3}
  let f : Nat → Nat := fun x => x
  show f 1 ≤ ∑ x ∈ s, f x := by
    simpa using (Finset.single_le_sum (s:=s) (f:=f) (by
      intro i hi; exact Nat.zero_le _
    ) (by decide : (1:Nat) ∈ s)
    )
  )
