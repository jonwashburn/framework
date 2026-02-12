import Mathlib

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Enumerate falsifier bands for ILG (PPN, lensing, GW). -/
structure Falsifiers where
  ppn_tight    : ℝ
  lensing_band : ℝ
  gw_band      : ℝ
  deriving Repr

/-- Predicate that falsifier bands are nonnegative (admissible). -/
def falsifiers_ok (f : Falsifiers) : Prop :=
  0 ≤ f.ppn_tight ∧ 0 ≤ f.lensing_band ∧ 0 ≤ f.gw_band

/-- Default admissible bands (illustrative). -/
def falsifiers_default : Falsifiers :=
  { ppn_tight := (1/100000 : ℝ)
  , lensing_band := 1
  , gw_band := (1/1000000 : ℝ) }

@[simp] theorem falsifiers_default_ok : falsifiers_ok falsifiers_default := by
  simp [falsifiers_ok, falsifiers_default]
  repeat' constructor <;> norm_num

end ILG
end Relativity
end IndisputableMonolith
