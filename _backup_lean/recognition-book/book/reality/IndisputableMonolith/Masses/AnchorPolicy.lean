import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Masses

structure AnchorPolicy where
  lambda : ℝ
  kappa  : ℝ

@[simp] noncomputable def anchorPolicyA : AnchorPolicy :=
  { lambda := Real.log Constants.phi, kappa := Constants.phi }

@[simp] def Z_quark (Q : ℤ) : ℤ := 4 + (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_lepton (Q : ℤ) : ℤ := (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_neutrino : ℤ := 0

structure ResidueLaw where
  f : ℝ → ℝ

structure SectorLaw where
  params  : SectorParams
  residue : ResidueLaw

end Masses
end IndisputableMonolith
