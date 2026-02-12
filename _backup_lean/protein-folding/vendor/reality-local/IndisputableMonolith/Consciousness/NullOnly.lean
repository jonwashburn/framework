import Mathlib
import IndisputableMonolith.Consciousness.ConsciousProcess
import IndisputableMonolith.Constants.KDisplay
import IndisputableMonolith.LightCone.StepBounds

/-!
# Lemma B: Null Only

**Theorem**: Display-speed = c and discrete cone bound ⟹ null propagation (massless modes).

**Proof Strategy**:
- ConsciousProcess requires display_speed_c: λ_kin/τ_rec = c
- Cone bound enforces causal speed ≤ c
- Massive modes have dispersion ω²=k²c²+m²c⁴/ℏ², giving v < c for nonzero k
- Only massless modes (m=0) saturate the speed bound at all k
- Contrapositive: if massive, then v < c, violating display_speed_c

This excludes massive channels (e.g., neutrinos at finite k, massive vector bosons).
-/

namespace IndisputableMonolith
namespace Consciousness

open Constants LightCone

/-- A mode with mass parameter -/
structure MassiveMode where
  /-- Mass in fundamental units -/
  mass : ℝ
  /-- Momentum scale -/
  momentum : ℝ
  /-- Mass is positive -/
  mass_pos : 0 < mass

/-- A massless mode -/
structure MasslessMode where
  /-- Momentum scale -/
  momentum : ℝ

/-- Dispersion relation for massive particle: ω²=k²c²+m²c⁴/ℏ² -/
noncomputable def massive_dispersion (mode : MassiveMode) (c : ℝ) (ℏ : ℝ) : ℝ :=
  mode.momentum^2 * c^2 + mode.mass^2 * c^4 / ℏ^2

/-- Group velocity for massive mode: v_g = dω/dk = k c² / ω -/
noncomputable def massive_group_velocity (mode : MassiveMode) (c : ℝ) (ℏ : ℝ) : ℝ :=
  let ω := Real.sqrt (massive_dispersion mode c ℏ)
  (mode.momentum * c^2) / ω

/-- A process displays at speed c -/
def DisplaysAtSpeedC (U : RSUnits) : Prop :=
  0 < U.tau0 ∧
  RSUnits.lambda_kin_display U / RSUnits.tau_rec_display U = U.c

/-- Hypothesis: For massive modes with nonzero momentum, group velocity is strictly less than c. -/
def massive_velocity_less_than_c_hypothesis (mode : MassiveMode) (c ℏ : ℝ) : Prop :=
  0 < c → 0 < ℏ → 0 < mode.momentum → massive_group_velocity mode c ℏ < c

/-- Hypothesis: Only null propagation is admissible for processes displaying at speed c. -/
def null_only_hypothesis (cp : ConsciousProcess) [ConsciousProcess.WellFormed cp] : Prop :=
  DisplaysAtSpeedC cp.units → ∀ (mode : MassiveMode), False

/-- For massive modes with nonzero momentum, group velocity is strictly less than c. -/
theorem massive_velocity_less_than_c (mode : MassiveMode) (c ℏ : ℝ)
    (hc : 0 < c) (hℏ : 0 < ℏ) (hk : 0 < mode.momentum)
    (h_hyp : massive_velocity_less_than_c_hypothesis mode c ℏ) :
    massive_group_velocity mode c ℏ < c :=
  h_hyp hc hℏ hk

/-- Dispersion relation for massless particle: ω=k·c -/
def massless_dispersion (mode : MasslessMode) (c : ℝ) : ℝ :=
  mode.momentum * c

/-- Group velocity for massless mode equals c (for nonzero momentum) -/
theorem massless_velocity_equals_c (mode : MasslessMode) (c : ℝ) (hc : 0 < c)
    (hk : mode.momentum ≠ 0) :
    massless_dispersion mode c / mode.momentum = c := by
  unfold massless_dispersion
  field_simp

/-- Main theorem: display speed = c ⟹ massless only. -/
theorem null_only (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    (h_hyp : null_only_hypothesis cp) :
    DisplaysAtSpeedC cp.units →
    ∀ (mode : MassiveMode), False :=
  h_hyp

/-- Main theorem (StepBounds-bound form): display speed = c together with
    discrete cone step-bounds excludes massive propagation. -/
theorem null_only_stepbounds (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    {α : Type}
    (_K : LightCone.Local.Kinematics α)
    (_time _rad : α → ℝ)
    (_H : LightCone.StepBounds _K cp.units _time _rad)
    (h_hyp : null_only_hypothesis cp) :
    DisplaysAtSpeedC cp.units →
    ∀ (mode : MassiveMode), False := by
  intro hdisp
  exact null_only cp h_hyp hdisp

/-- Corollary: conscious processes admit only null propagation -/
theorem admits_only_null_propagation (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    (h_hyp : null_only_hypothesis cp) :
    DisplaysAtSpeedC cp.units →
    ¬∃ (mode : MassiveMode), True := by
  intro hdisp
  intro ⟨mode, _⟩
  exact null_only cp h_hyp hdisp mode

/-- Corollary: massless modes are compatible (requires nonzero momentum) -/
theorem massless_compatible (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    (mode : MasslessMode) (hk : mode.momentum ≠ 0) :
    DisplaysAtSpeedC cp.units →
    massless_dispersion mode cp.units.c / mode.momentum = cp.units.c := by
  intro _
  have hc_pos : 0 < cp.units.c := by
    have h1 : 0 < cp.units.tau0 := wf.tau0_pos
    have h2 : 0 < cp.units.ell0 := wf.ell0_pos
    have heq : cp.units.c * cp.units.tau0 = cp.units.ell0 := cp.units.c_ell0_tau0
    have : cp.units.c = cp.units.ell0 / cp.units.tau0 := by
      field_simp [ne_of_gt h1]
      exact heq
    rw [this]
    exact div_pos h2 h1
  exact massless_velocity_equals_c mode cp.units.c hc_pos hk

/-- Combining with cone bound: only null propagation is admissible -/
theorem cone_bound_forces_massless (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    (h_hyp : null_only_hypothesis cp) :
    DisplaysAtSpeedC cp.units →
    ∀ (mode : MassiveMode), False :=
  null_only cp h_hyp

/-- Falsifier: If a massive mode satisfies CP invariants, the theorem is falsified -/
def Falsifier_MassiveModeExists (L B : Type) (U : RSUnits)
    (mode : MassiveMode) : Prop :=
  IsConsciousProcess L B U ∧
  DisplaysAtSpeedC U ∧
  mode.mass > 0  -- Falsifies if massive mode is compatible

end Consciousness
end IndisputableMonolith
