import Mathlib

/-
Riesz semicontinuity surrogate (spectral slab via gap)
Keep it Prop-native; H is ignored by design.
-/

section

variable {α : Type*}

/-- A spec-level "spectral slab" predicate: currently just the positivity of `γ`. -/
def specSlabOp (H : α) (γ : ℝ) : Prop :=
  0 < γ

/-- If the gap `γ` is positive, the slab predicate holds. -/
theorem specSlabOp_of_pos {H : α} {γ : ℝ} (hγ : 0 < γ) : specSlabOp H γ :=
  hγ

/-- The predicate is definitionally equivalent to `0 < γ`. -/
theorem specSlabOp_iff {H : α} {γ : ℝ} : specSlabOp H γ ↔ 0 < γ :=
  Iff.rfl

end
