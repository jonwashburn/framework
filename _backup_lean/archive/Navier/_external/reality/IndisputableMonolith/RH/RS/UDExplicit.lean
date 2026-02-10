import IndisputableMonolith.RH.RS.Spec

namespace IndisputableMonolith
namespace RH
namespace RS

/-- Minimal explicit universal dimless witness (reuses existing UD_explicit). -/
noncomputable abbrev UD_minimal (φ : ℝ) : UniversalDimless φ := UD_explicit φ

/-- Existence part: trivial bridge and explicit UD witness. -/
noncomputable def exists_bridge_and_UD (φ : ℝ) (L : Ledger) :
  ∃ B : Bridge L, ∃ U : UniversalDimless φ, Matches φ L B U := by
  refine ⟨⟨()⟩, ⟨UD_explicit φ, ?h⟩⟩
  -- `Matches` is inhabited by `matches_explicit`
  exact matches_explicit φ L ⟨()⟩

/-- Units equivalence by value equality -/
def unitsEqv_byValue (L : Ledger) : UnitsEqv L :=
{ Rel := fun x y => x.value = y.value
, refl := by intro x; rfl
, symm := by intro x y h; exact h.symm
, trans := by intro x y z hxy hyz; exact hxy.trans hyz }

end RS
end RH
end IndisputableMonolith
