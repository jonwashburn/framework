import Mathlib
import IndisputableMonolith.Verification.MeaningPeriodicTable.ModePhiTauGaugeClosure

/-!
## Light-Language Meaning (τ modulo gauge; forcing kernel)

This module upgrades the previous placeholder `Meaning := []` to a nontrivial meaning object:
the **τ-mod-gauge** quotient of a forced WToken signature.

What is modeled here (and machine-checked in the imported periodic-table modules):

- **mode family** is extracted by a frozen deterministic classifier (`forcedModeFamily`)
- **φ-level** is forced by RS argmin on the φ-lattice (`forcedPhiLevel`)
- **τ** is **not** treated as semantic data; it is quotiented out by phase gauge (`TauModuloGauge`)

This is intentionally only the token/signature forcing layer. End-to-end LNAL normal-form
meaning is handled elsewhere (and remains scaffolded).
-/
namespace LightLanguage.CPM

open scoped Classical

namespace MeaningForced

open IndisputableMonolith
open IndisputableMonolith.Verification
open IndisputableMonolith.Verification.MeaningPeriodicTable
open IndisputableMonolith.Water

/-! ### Meaning object -/

/-- The meaning object for a window: τ modulo gauge (a quotient type). -/
abbrev MeaningObject : Type :=
  TauModuloGauge

/-! ### Forced signature representative -/

/-- Canonical representative: we always choose `τ = τ0` because τ is eliminated in the quotient. -/
noncomputable def forcedSignature (m : Water.WTokenMode) (phi : Water.PhiLevel) :
    ModePhiTauSignature :=
  { modeFamily := m
    phiLevel := phi
    tauVariant := Water.TauOffset.tau0
    tau_legal := by intro _; rfl }

/-! ### Forced meaning map -/

/-- Meaning of an 8-beat window, when the classifier returns an exact mode family. -/
noncomputable def Meaning (v : Fin 8 → ℂ) (r : ℝ) (hr : 0 < r) : Option MeaningObject :=
  match forcedModeFamily v with
  | none => none
  | some m =>
      let phi := forcedPhiLevel r hr
      some (forcedSignature m phi).tauModGauge

/-- Semantic equivalence for windows (at fixed extracted radius `r`). -/
def SemanticEquivalence (v₁ v₂ : Fin 8 → ℂ) (r : ℝ) (hr : 0 < r) : Prop :=
  Meaning v₁ r hr = Meaning v₂ r hr

/-! ### Small interface lemmas -/

theorem Meaning_eq_some_iff (v : Fin 8 → ℂ) (r : ℝ) (hr : 0 < r) (M : MeaningObject) :
    Meaning v r hr = some M ↔
      ∃ m : Water.WTokenMode,
        forcedModeFamily v = some m ∧
          M = (forcedSignature m (forcedPhiLevel r hr)).tauModGauge := by
  cases h : forcedModeFamily v with
  | none =>
      simp [Meaning, h]
  | some m =>
      -- `simp` reduces this case to a symmetric equality; close with `eq_comm`.
      simpa [Meaning, h, forcedSignature, eq_comm]

end MeaningForced
end LightLanguage.CPM
