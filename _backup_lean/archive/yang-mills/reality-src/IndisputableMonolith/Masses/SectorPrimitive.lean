import Mathlib
import IndisputableMonolith.Masses.Ribbons

namespace IndisputableMonolith
namespace Masses
namespace SectorPrimitive

structure Primitive where
  word : Ribbons.Word
  reduced : Ribbons.normalForm word = word

@[simp] def deltaOf (gen : Ribbons.GenClass) (p : Primitive) : ℤ :=
  Ribbons.rungFrom gen p.word

lemma delta_invariant (p : Primitive) (gen : Ribbons.GenClass) :
  deltaOf gen p = deltaOf gen p := rfl

end SectorPrimitive
end Masses
end IndisputableMonolith
