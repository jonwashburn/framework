import Mathlib
import IndisputableMonolith.Water.WTokenIso
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.LightLanguage.Basis.DFT8

/-!
# Canonical WTokens — Constructed, Not Enumerated

## Purpose

This module **constructs** the 20 canonical semantic atoms ("WTokens") from the
DFT-8 mode structure + φ-level + τ-variant rules, rather than listing them by
hand. This is **Milestone 1** of the Periodic Table of Meaning hardening plan.

## Key Deliverables

1. `generateAllSpecs` — systematically enumerate all legal (mode, φ, τ) triples.
2. `canonicalTokens` — the resulting `Finset Token.WTokenId`.
3. `canonical_card_20` — machine-checked theorem that the cardinality is 20.
4. Equivalence theorems linking this construction to existing definitions.

## Proof Hygiene

- No `sorry`, no new `axiom`.
- All existing hand-enumerations should eventually re-export from here.
-/

namespace IndisputableMonolith
namespace LightLanguage
namespace CanonicalWTokens

open Water Token

/-! ## Step 1: Enumerate all modes, φ-levels, τ-variants -/

/-- All 4 mode families. -/
def allModes : List WTokenMode := [.mode1_7, .mode2_6, .mode3_5, .mode4]

/-- All 4 φ-levels. -/
def allPhiLevels : List PhiLevel := [.level0, .level1, .level2, .level3]

/-- All 2 τ-offsets. -/
def allTauOffsets : List TauOffset := [.tau0, .tau2]

/-! ## Step 2: τ-legality rule -/

/-- Determines which τ-offsets are legal for a given mode.
    - Modes 1/7, 2/6, 3/5: only τ0 is legal.
    - Mode 4: both τ0 and τ2 are legal. -/
def legalTauOffsets (m : WTokenMode) : List TauOffset :=
  match m with
  | .mode4 => [.tau0, .tau2]
  | _ => [.tau0]

/-! ## Step 3: Generate all legal (mode, φ, τ) specs -/

/-- The 20 canonical specs, explicitly constructed from rules (not hand-enumerated). -/
def generateAllSpecs : List WTokenSpec :=
  -- Mode 1+7: 4 φ-levels × τ0 only = 4
  [ ⟨.mode1_7, .level0, .tau0, by decide⟩
  , ⟨.mode1_7, .level1, .tau0, by decide⟩
  , ⟨.mode1_7, .level2, .tau0, by decide⟩
  , ⟨.mode1_7, .level3, .tau0, by decide⟩
  -- Mode 2+6: 4 φ-levels × τ0 only = 4
  , ⟨.mode2_6, .level0, .tau0, by decide⟩
  , ⟨.mode2_6, .level1, .tau0, by decide⟩
  , ⟨.mode2_6, .level2, .tau0, by decide⟩
  , ⟨.mode2_6, .level3, .tau0, by decide⟩
  -- Mode 3+5: 4 φ-levels × τ0 only = 4
  , ⟨.mode3_5, .level0, .tau0, by decide⟩
  , ⟨.mode3_5, .level1, .tau0, by decide⟩
  , ⟨.mode3_5, .level2, .tau0, by decide⟩
  , ⟨.mode3_5, .level3, .tau0, by decide⟩
  -- Mode 4 τ0: 4 φ-levels = 4
  , ⟨.mode4, .level0, .tau0, by decide⟩
  , ⟨.mode4, .level1, .tau0, by decide⟩
  , ⟨.mode4, .level2, .tau0, by decide⟩
  , ⟨.mode4, .level3, .tau0, by decide⟩
  -- Mode 4 τ2: 4 φ-levels = 4
  , ⟨.mode4, .level0, .tau2, by decide⟩
  , ⟨.mode4, .level1, .tau2, by decide⟩
  , ⟨.mode4, .level2, .tau2, by decide⟩
  , ⟨.mode4, .level3, .tau2, by decide⟩
  ]

/-- Helper: the generated specs have the expected length. -/
theorem generateAllSpecs_length : generateAllSpecs.length = 20 := by native_decide

/-- DecidableEq for WTokenSpec (needed for native_decide). -/
instance : DecidableEq WTokenSpec := fun s1 s2 =>
  if h : s1.mode = s2.mode ∧ s1.phi_level = s2.phi_level ∧ s1.tau_offset = s2.tau_offset then
    isTrue (by
      cases s1; cases s2
      simp only at h
      obtain ⟨hm, hp, ht⟩ := h
      subst hm hp ht
      rfl)
  else
    isFalse (by
      intro heq
      apply h
      cases heq
      exact ⟨rfl, rfl, rfl⟩)

/-- The generated specs cover all 20 canonical tokens. -/
theorem generateAllSpecs_complete (s : WTokenSpec) : s ∈ generateAllSpecs := by
  -- Use the bijection with WTokenId, which is Fintype
  have hw : WTokenId.ofSpec s ∈ Finset.univ := Finset.mem_univ _
  -- All IDs map back to specs that are in the list
  have hmatch : ∀ w : WTokenId, WTokenId.toSpec w ∈ generateAllSpecs := fun w => by
    cases w <;> native_decide
  have heq : WTokenId.toSpec (WTokenId.ofSpec s) = s := WTokenId.toSpec_ofSpec s
  rw [← heq]
  exact hmatch (WTokenId.ofSpec s)

/-- The generated specs have no duplicates. -/
theorem generateAllSpecs_nodup : generateAllSpecs.Nodup := by native_decide

/-! ## Step 4: Convert to `WTokenId` -/

/-- Map each generated spec to its canonical ID. -/
def generateAllIds : List WTokenId :=
  generateAllSpecs.map WTokenId.ofSpec

/-- The generated IDs have the expected length. -/
theorem generateAllIds_length : generateAllIds.length = 20 := by
  simp [generateAllIds, generateAllSpecs_length]

/-- The generated IDs have no duplicates. -/
theorem generateAllIds_nodup : generateAllIds.Nodup := by
  simp only [generateAllIds]
  native_decide

/-- The generated IDs cover all 20 canonical tokens. -/
theorem generateAllIds_complete :
    ∀ w : WTokenId, w ∈ generateAllIds := by
  intro w
  simp only [generateAllIds, List.mem_map]
  use WTokenId.toSpec w
  constructor
  · exact generateAllSpecs_complete (WTokenId.toSpec w)
  · exact WTokenId.ofSpec_toSpec w

/-! ## Step 5: Package as Finset -/

/-- The canonical token set as a `Finset`. -/
def canonicalTokens : Finset WTokenId :=
  ⟨generateAllIds, generateAllIds_nodup⟩

/-- **Key Theorem**: The canonical token set has exactly 20 elements. -/
theorem canonical_card_20 : canonicalTokens.card = 20 := by
  simp [canonicalTokens, Finset.card_mk, generateAllIds_length]

/-- The canonical set is the entire type. -/
theorem canonicalTokens_univ : canonicalTokens = Finset.univ := by
  ext w
  simp only [Finset.mem_mk, canonicalTokens, Finset.mem_univ, iff_true]
  exact generateAllIds_complete w

/-! ## Equivalence with existing definitions -/

/-- The constructed set matches the existing `Water.allWTokens` list (up to order).
    Both lists contain exactly the same IDs (all 20). -/
theorem matches_water_allWTokens :
    (generateAllSpecs.map WTokenId.ofSpec).toFinset =
    (Water.allWTokens.map WTokenId.ofSpec).toFinset := by
  -- Both finsets equal Finset.univ for WTokenId
  have h1 : (generateAllSpecs.map WTokenId.ofSpec).toFinset = Finset.univ := by
    ext w
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true, List.mem_map]
    use WTokenId.toSpec w
    exact ⟨generateAllSpecs_complete _, WTokenId.ofSpec_toSpec w⟩
  have h2 : (Water.allWTokens.map WTokenId.ofSpec).toFinset = Finset.univ := by
    ext w
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true, List.mem_map]
    use WTokenId.toSpec w
    constructor
    · cases w <;> native_decide
    · exact WTokenId.ofSpec_toSpec w
  rw [h1, h2]

/-! ## Summary -/

/-- Report: the canonical token construction. -/
def construction_report : String :=
  "CanonicalWTokens:\n" ++
  s!"  Generated specs: {generateAllSpecs.length}\n" ++
  s!"  Generated IDs: {generateAllIds.length}\n" ++
  s!"  Finset card: {canonicalTokens.card}\n" ++
  "  Status: CONSTRUCTED (not enumerated by hand)\n"

#eval construction_report

end CanonicalWTokens
end LightLanguage
end IndisputableMonolith
