import Mathlib
import IndisputableMonolith.LightLanguage.CPM.Meaning

/-!
# Perfect Language Certificate (meaning-forcing kernel)

This module is the peer-review-facing **machine-checked kernel** behind the claim
that ULL meaning is *forced* (and not an arbitrary convention), at the token/signature layer.

What is proved here (Lean-verified):

- **φ-level forcing**: for any positive ratio `r > 0`, the forced φ-level minimizes the canonical
  mismatch cost \(J(r/\varphi^k)\) over the finite ladder \(k\in\{0,1,2,3\}\).
- **τ carries no semantic degree of freedom** beyond phase gauge: two legal τ-variants with the
  same `(modeFamily, φLevel)` induce the same element of the quotient type “τ modulo gauge”.

What is *not* proved here (still separate work):

- end-to-end LNAL normal-form meaning for arbitrary full signals,
- completeness/minimality of the full motif grammar,
- the full “perfect language uniqueness” story.

Lean sources for the proved components live in:

- `IndisputableMonolith.Verification.MeaningPeriodicTable.ModePhiClosure`
- `IndisputableMonolith.Verification.MeaningPeriodicTable.ModePhiTauGaugeClosure`
- `IndisputableMonolith.LightLanguage.CPM.Meaning` (exports the meaning map into a quotient type)
-/

namespace LightLanguage

open scoped Classical

namespace MeaningCert

open IndisputableMonolith
open IndisputableMonolith.Verification.MeaningPeriodicTable
open IndisputableMonolith.Water

/-! ## Certificate -/

structure PerfectLanguageCert where
  /-- φ-level forcing: the forced φ-level is an argmin of the RS mismatch cost over the finite ladder. -/
  phiLevel_forced :
      ∀ (r : ℝ) (hr : 0 < r) (level : Foundation.ReferenceWToken.PhiLevel),
        Cost.Jcost
            (r / Constants.phi ^
                (Foundation.WTokenReference.phiLevelExponent
                    (refPhiLevelOfWater (forcedPhiLevel r hr)) : ℝ))
          ≤
        Cost.Jcost
            (r / Constants.phi ^
                (Foundation.WTokenReference.phiLevelExponent level : ℝ))

  /-- τ is not semantic data beyond the phase-gauge quotient (“τ modulo gauge”). -/
  tau_quotiented :
      ∀ (m : Water.WTokenMode) (phi : Water.PhiLevel)
        (tau tau' : Water.TauOffset)
        (hτ : m ≠ Water.WTokenMode.mode4 → tau = Water.TauOffset.tau0)
        (hτ' : m ≠ Water.WTokenMode.mode4 → tau' = Water.TauOffset.tau0),
        (ModePhiTauSignature.tauModGauge
            { modeFamily := m
              phiLevel := phi
              tauVariant := tau
              tau_legal := hτ })
          =
        (ModePhiTauSignature.tauModGauge
            { modeFamily := m
              phiLevel := phi
              tauVariant := tau'
              tau_legal := hτ' })

theorem perfect_language_cert_holds : PerfectLanguageCert := by
  refine ⟨?phi_forced, ?tau_q⟩
  · intro r hr level
    -- This is exactly the theorem proved in `ModePhiClosure`.
    simpa using (forcedPhiLevel_minimizes_reference (r := r) (hr := hr) level)
  · intro m phi tau tau' hτ hτ'
    -- τ is eliminated in the quotient: show gauge equivalence, then apply quotient equality.
    have hg :
        ModePhiTauSignature.GaugeEq
          { modeFamily := m
            phiLevel := phi
            tauVariant := tau
            tau_legal := hτ }
          { modeFamily := m
            phiLevel := phi
            tauVariant := tau'
            tau_legal := hτ' } := by
      -- Same `(modeFamily, phiLevel)` implies gauge equivalence (τ differs only by phase).
      exact ModePhiTauSignature.gaugeEq_of_same_modePhi _ _ rfl rfl
    exact (ModePhiTauSignature.tauModGauge_eq_iff _ _).2 hg

end MeaningCert

end LightLanguage

/-! ## URC-facing report wrapper -/

namespace URCGenerators

def perfect_language_report : String :=
  "PerfectLanguageCert (meaning-forcing kernel): PROVEN ✓\n" ++
  "  ├─ φ-level forcing: argmin on finite φ-lattice (PROVEN)\n" ++
  "  └─ τ is not meaning: τ quotient modulo global phase gauge (PROVEN)\n\n" ++
  "Note: End-to-end LNAL normal-form meaning and full perfect-language uniqueness\n" ++
  "are separate work and are not claimed by this kernel."

end URCGenerators
