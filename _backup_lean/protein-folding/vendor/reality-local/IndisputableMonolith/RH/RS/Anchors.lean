import Mathlib

namespace IndisputableMonolith
namespace RH
namespace RS

/-- Measurement anchors (minimal interface used by band checks). -/
structure Anchors where
  a1 : ℝ
  a2 : ℝ
  /-- Calibration consistency: if the time anchor vanishes, the length anchor must
      also vanish so that `c * tau0 = ell0` remains solvable. -/
  consistent : a1 = 0 → a2 = 0

namespace Anchors

@[simp] lemma consistent_zero (A : Anchors) : A.a1 = 0 → A.a2 = 0 :=
  A.consistent

end Anchors

end RS
end RH
end IndisputableMonolith
