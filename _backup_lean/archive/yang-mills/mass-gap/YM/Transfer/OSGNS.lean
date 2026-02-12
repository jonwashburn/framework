import Mathlib
import YM.OSPositivity.GNS

/-!
Small adapter that re-exports a concrete OS/GNS transfer suitable for the
framework to consume without changing its existing `TransferOperator` type.

Reference (Yang-Mills-sept21.tex): 305–309.
-/

namespace YM.Transfer.OSGNS

export YM.OSPositivity.GNS (OSStateSpace transferZero
  transferZero_isSelfAdjoint transferZero_positive_real_part
  transfer_op transfer_isSelfAdjoint transfer_positive_real_part)

end YM.Transfer.OSGNS


