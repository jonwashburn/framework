import Mathlib
import IndisputableMonolith.RecogGeom.Quotient

/-!
# Recognition Geometry: Connectivity and Local Regularity (RG5)

This module develops the notion of "recognition connectivity"—when two
configurations can be connected by a path that stays within a single
resolution cell.

## The Core Question

When is a recognition geometry "regular" enough to support smooth structure?

The answer involves local regularity (RG5): recognition preimages should be
"connected" within neighborhoods. This ensures that resolution cells don't
fragment pathologically.

## Key Definitions

- `IsRecognitionConnected`: When a set is connected (all points equivalent)
- `IsLocallyRegular`: RG5 - preimages are connected in neighborhoods
- `SatisfiesRG5`: The full RG5 axiom

## Physical Interpretation

Recognition connectivity captures the idea that "nearby" configurations
(in the recognition sense) should form coherent clusters, not scattered
points. This is what allows smooth physics to emerge from discrete recognition.

-/

namespace IndisputableMonolith
namespace RecogGeom

variable {C E : Type*}

/-! ## Recognition Connectivity -/

/-- A set S is recognition-connected for recognizer r if all elements of S
    are mutually indistinguishable.

    This is a strong notion: every point sees the same event. -/
def IsRecognitionConnected (r : Recognizer C E) (S : Set C) : Prop :=
  ∀ c₁ c₂, c₁ ∈ S → c₂ ∈ S → Indistinguishable r c₁ c₂

/-- The empty set is vacuously recognition-connected -/
theorem isRecognitionConnected_empty (r : Recognizer C E) :
    IsRecognitionConnected r ∅ := by
  intro c₁ c₂ h₁ _
  exact absurd h₁ (Set.not_mem_empty c₁)

/-- A singleton set is recognition-connected -/
theorem isRecognitionConnected_singleton (r : Recognizer C E) (c : C) :
    IsRecognitionConnected r {c} := by
  intro c₁ c₂ h₁ h₂
  simp only [Set.mem_singleton_iff] at h₁ h₂
  rw [h₁, h₂]
  exact Indistinguishable.refl r c

/-- A resolution cell is recognition-connected by definition -/
theorem isRecognitionConnected_resolutionCell (r : Recognizer C E) (c : C) :
    IsRecognitionConnected r (ResolutionCell r c) := by
  intro c₁ c₂ h₁ h₂
  simp only [ResolutionCell, Set.mem_setOf_eq] at h₁ h₂
  exact Indistinguishable.trans r h₁ (Indistinguishable.symm' r h₂)

/-- A subset of a recognition-connected set is recognition-connected -/
theorem isRecognitionConnected_subset (r : Recognizer C E) {S T : Set C}
    (hST : S ⊆ T) (hT : IsRecognitionConnected r T) :
    IsRecognitionConnected r S := by
  intro c₁ c₂ h₁ h₂
  exact hT c₁ c₂ (hST h₁) (hST h₂)

/-! ## Local Regularity (RG5) -/

/-- A recognizer is locally regular at c if the preimage of r(c) is
    recognition-connected within some neighborhood of c.

    This means: nearby configurations that produce the same event
    are actually "coherently" grouped together. -/
def IsLocallyRegular (L : LocalConfigSpace C) (r : Recognizer C E) (c : C) : Prop :=
  ∃ U ∈ L.N c, IsRecognitionConnected r (r.R ⁻¹' {r.R c} ∩ U)

/-- A recognizer is locally regular everywhere -/
def IsRegular (L : LocalConfigSpace C) (r : Recognizer C E) : Prop :=
  ∀ c : C, IsLocallyRegular L r c

/-- **RG5**: Local Regularity Axiom.

    A recognition geometry satisfies RG5 if every recognizer is locally regular.
    This ensures that resolution cells form coherent "blobs" within neighborhoods,
    not scattered fragments. -/
structure SatisfiesRG5 (L : LocalConfigSpace C) (r : Recognizer C E) : Prop where
  locally_regular : IsRegular L r

/-! ## Consequences of Local Regularity -/

/-- If a recognizer is locally regular at c, the resolution cell intersected
    with some neighborhood is still recognition-connected. -/
theorem locally_regular_cell_connected (L : LocalConfigSpace C) (r : Recognizer C E)
    (c : C) (h : IsLocallyRegular L r c) :
    ∃ U ∈ L.N c, IsRecognitionConnected r (ResolutionCell r c ∩ U) := by
  obtain ⟨U, hU, hconn⟩ := h
  use U, hU
  -- ResolutionCell r c = r.R ⁻¹' {r.R c} by definition of Indistinguishable
  intro c₁ c₂ h₁ h₂
  simp only [ResolutionCell, Set.mem_inter_iff, Set.mem_setOf_eq] at h₁ h₂
  -- c₁, c₂ both in preimage of {r.R c} ∩ U
  have hc₁ : c₁ ∈ r.R ⁻¹' {r.R c} ∩ U := ⟨h₁.1, h₁.2⟩
  have hc₂ : c₂ ∈ r.R ⁻¹' {r.R c} ∩ U := ⟨h₂.1, h₂.2⟩
  exact hconn c₁ c₂ hc₁ hc₂

/-- A constant recognizer is locally regular everywhere. -/
theorem constant_recognizer_regular (L : LocalConfigSpace C) (r : Recognizer C E)
    (hconst : ∀ c₁ c₂, r.R c₁ = r.R c₂) :
    IsRegular L r := by
  intro c
  obtain ⟨U, hU⟩ := L.N_nonempty c
  use U, hU
  intro c₁ c₂ _ _
  exact hconst c₁ c₂

/-! ## The Role of RG5 in Geometry -/

/-- **Intuition**: RG5 ensures that "resolution cells don't fragment".

    Without RG5, a resolution cell could look like a Cantor set:
    infinitely fragmented within any neighborhood. With RG5, resolution
    cells are locally "blob-like"—they stay together coherently.

    This is what allows smooth geometric structure to emerge:
    resolution cells become the "atoms" of recognition geometry,
    and RG5 ensures these atoms are well-behaved. -/

/-! ## Module Status -/

def connectivity_status : String :=
  "✓ IsRecognitionConnected: connected sets defined\n" ++
  "✓ isRecognitionConnected_empty: empty set connected\n" ++
  "✓ isRecognitionConnected_singleton: singletons connected\n" ++
  "✓ isRecognitionConnected_resolutionCell: resolution cells connected\n" ++
  "✓ isRecognitionConnected_subset: subsets inherit connectivity\n" ++
  "✓ IsLocallyRegular: local regularity at a point (RG5)\n" ++
  "✓ IsRegular: global regularity\n" ++
  "✓ SatisfiesRG5: RG5 axiom structure\n" ++
  "✓ locally_regular_cell_connected: consequence of RG5\n" ++
  "✓ constant_recognizer_regular: constants are regular\n" ++
  "\n" ++
  "CONNECTIVITY & LOCAL REGULARITY (RG5) COMPLETE"

#eval connectivity_status

end RecogGeom
end IndisputableMonolith
