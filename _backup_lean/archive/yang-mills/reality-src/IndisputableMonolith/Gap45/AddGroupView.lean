import Mathlib

namespace IndisputableMonolith
namespace Gap45
namespace AddGroupView

open Nat

/-- Additive version: if `(8) • a = 0` and `(45) • a = 0`, then the additive order of `a`
divides `gcd(8,45)=1`, hence `a = 0`. -/
lemma trivial_intersection_nsmul {A : Type*} [AddGroup A] {a : A}
  (h8 : (8 : ℕ) • a = 0) (h45 : (45 : ℕ) • a = 0) : a = 0 := by
  have h8d : addOrderOf a ∣ 8 := (addOrderOf_dvd_iff_nsmul_eq_zero (a:=a) (n:=8)).2 h8
  have h45d : addOrderOf a ∣ 45 := (addOrderOf_dvd_iff_nsmul_eq_zero (a:=a) (n:=45)).2 h45
  have hgcd : addOrderOf a ∣ Nat.gcd 8 45 := Nat.dvd_gcd h8d h45d
  have hone : addOrderOf a ∣ 1 := by simpa using hgcd
  have h1 : addOrderOf a = 1 := Nat.dvd_one.mp hone
  simpa [h1] using (addOrderOf_eq_one_iff.mpr rfl)

end AddGroupView
end Gap45
end IndisputableMonolith
