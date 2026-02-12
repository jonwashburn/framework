import Mathlib
-- import IndisputableMonolith.Measurement
import IndisputableMonolith.Patterns
import IndisputableMonolith.RH.RS.Spec
-- import IndisputableMonolith.Quantum

namespace IndisputableMonolith
namespace RH
namespace RS
namespace Witness

/-- Eight‑tick minimality witness tied to `Patterns` theorem. -/
def eightTickMinimalHolds : Prop :=
  ∃ w : IndisputableMonolith.Patterns.CompleteCover 3, w.period = 8

/-- Born rule witness interface: existence of a measurement pipeline whose averaging
    recovers a window integer (DNARP bridge). -/
def bornHolds : Prop :=
  ∃ (w : IndisputableMonolith.Patterns.Pattern 8),
    IndisputableMonolith.Measurement.observeAvg8 1 (IndisputableMonolith.Measurement.extendPeriodic8 w)
      = IndisputableMonolith.Measurement.Z_of_window w

/-- Bose–Fermi witness: provide a concrete interface instance from a trivial path system. -/
def boseFermiHolds : Prop :=
  IndisputableMonolith.Quantum.BoseFermiIface PUnit
    ({ C := fun _ => 0
     , comp := fun _ _ => PUnit.unit
     , cost_additive := by intro _ _; simp
     , normSet := { PUnit.unit }
     , sum_prob_eq_one := by
         -- sum over singleton = exp(0) = 1
         simp [IndisputableMonolith.Quantum.PathWeight.prob] })

/-- Minimal witnesses for the above props. -/
theorem eightTick_from_TruthCore : eightTickMinimalHolds := by
  refine ⟨IndisputableMonolith.Patterns.grayCoverQ3, ?_⟩
  simpa using IndisputableMonolith.Patterns.period_exactly_8

theorem born_from_TruthCore : bornHolds := by
  refine ⟨IndisputableMonolith.Patterns.grayWindow, ?_⟩
  have hk : (1 : Nat) ≠ 0 := by decide
  simpa using IndisputableMonolith.Measurement.observeAvg8_periodic_eq_Z (k:=1) hk _

theorem boseFermi_from_TruthCore : boseFermiHolds := by
  -- Derived from the generic RS pathweight interface
  simpa using
    (IndisputableMonolith.Quantum.rs_pathweight_iface PUnit
      { C := fun _ => 0
      , comp := fun _ _ => PUnit.unit
      , cost_additive := by intro _ _; simp
      , normSet := { PUnit.unit }
      , sum_prob_eq_one := by simp [IndisputableMonolith.Quantum.PathWeight.prob] }).right

/-- Historical alias: now redirects to the explicit φ‑closed target in `Spec`. -/
noncomputable def UD_minimal (φ : ℝ) : RH.RS.UniversalDimless φ :=
  RH.RS.UD_explicit φ

/-- Historical alias: now mirrors the explicit `dimlessPack_explicit` from `Spec`. -/
noncomputable def dimlessPack_minimal (L : RH.RS.Ledger) (B : RH.RS.Bridge L) : RH.RS.DimlessPack L B :=
  RH.RS.dimlessPack_explicit L B

/-- Matches holds for the explicit universal pack (alias to `Spec.matches_explicit`). -/
theorem matches_minimal (φ : ℝ) (L : RH.RS.Ledger) (B : RH.RS.Bridge L) :
  RH.RS.Matches φ L B (UD_minimal φ) := by
  simpa [UD_minimal, dimlessPack_minimal] using RH.RS.matches_explicit φ L B

/-- Combined witness: Matches plus the TruthCore-provided proofs for the three props. -/
theorem matches_withTruthCore (φ : ℝ) (L : RH.RS.Ledger) (B : RH.RS.Bridge L) :
  RH.RS.Matches φ L B (UD_minimal φ)
  ∧ eightTickMinimalHolds ∧ bornHolds ∧ boseFermiHolds := by
  refine And.intro (matches_minimal φ L B) ?rest
  refine And.intro eightTick_from_TruthCore (And.intro born_from_TruthCore boseFermi_from_TruthCore)

/-- Strong inevitability: alias to the strengthened inevitability in `Spec`. -/
theorem inevitability_dimless_partial (φ : ℝ) : RH.RS.Inevitability_dimless φ :=
  RH.RS.inevitability_dimless_strong φ

end Witness
end RS
end RH
end IndisputableMonolith
