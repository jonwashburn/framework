import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Analysis.Complex.Basic

noncomputable section

open scoped TensorProduct

namespace Scratch

#check LinearMap.mul' ℝ ℂ
#check (RingHom.toLinearMap (TensorProduct.lmul' (S := ℂ) ℝ : _))

end Scratch
