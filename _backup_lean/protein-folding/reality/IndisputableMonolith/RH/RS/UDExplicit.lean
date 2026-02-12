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

/-- Minimal uniqueness: use the units equivalence relation as universal relation. -/
def unitsEqv_trivial (L : Ledger) : UnitsEqv L :=
{ Rel := fun _ _ => True
, refl := by intro _; trivial
, symm := by intro _ _ _; trivial
, trans := by intro _ _ _ _ _; trivial }

end RS
end RH
end IndisputableMonolith
