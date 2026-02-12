import Mathlib
import IndisputableMonolith.Constants

open IndisputableMonolith.Constants

#check zpow_neg_one
#check zpow_neg
#check zpow_two
#check zpow_bit0
#check zpow_add
#check zpow_mul

-- quick simp check
example : phi ^ (-(2:ℤ)) = (phi ^ (-1:ℤ))^2 := by
  -- expect by simp?
  ring_nf

