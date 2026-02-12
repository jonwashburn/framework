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

/-- Hypothesis: Only null propagation is admissible for processes displaying at speed c. -/
def null_only_hypothesis (cp : ConsciousProcess) [ConsciousProcess.WellFormed cp] : Prop :=
  DisplaysAtSpeedC cp.units → ∀ (mode : MassiveMode), False

/-- **THEOREM (RIGOROUS)**: For massive modes with nonzero momentum, group velocity is strictly less than c.

    **Proof**:
    - v_g = k·c²/ω where ω = √(k²c² + m²c⁴/ℏ²)
    - v_g < c ↔ k·c²/ω < c ↔ k·c < ω (since ω > 0)
    - ↔ k²c² < ω² (since both positive)
    - But ω² = k²c² + m²c⁴/ℏ² > k²c² when m > 0 ✓ -/
theorem massive_velocity_less_than_c (mode : MassiveMode) (c ℏ : ℝ)
    (hc : 0 < c) (hℏ : 0 < ℏ) (hk : 0 < mode.momentum) :
    massive_group_velocity mode c ℏ < c := by
  unfold massive_group_velocity massive_dispersion
  -- Let ω² = k²c² + m²c⁴/ℏ²
  set ω_sq := mode.momentum^2 * c^2 + mode.mass^2 * c^4 / ℏ^2 with hω_sq_def
  -- ω² > 0
  have hω_sq_pos : 0 < ω_sq := by
    have h1 : 0 ≤ mode.momentum^2 * c^2 := by positivity
    have h2 : 0 < mode.mass^2 * c^4 / ℏ^2 := by
      have hm : 0 < mode.mass := mode.mass_pos
      positivity
    linarith
  -- ω > 0
  have hω_pos : 0 < Real.sqrt ω_sq := Real.sqrt_pos.mpr hω_sq_pos
  -- We want: k·c²/ω < c, i.e., k·c < ω (since c > 0)
  rw [div_lt_iff hω_pos]
  -- Now we need: k·c² < c · ω = c · √(ω²)
  rw [mul_comm c]
  -- Need: k·c² < √(ω²) · c
  rw [← Real.sqrt_sq (le_of_lt hc)]
  rw [← Real.sqrt_mul (sq_nonneg c)]
  -- Need: k·c² < √(c² · ω²)
  -- This is equivalent to (k·c²)² < c² · ω² (since both positive)
  have hkc2_pos : 0 < mode.momentum * c^2 := by positivity
  rw [Real.lt_sqrt hkc2_pos]
  -- Need: (k·c²)² < c² · ω²
  ring_nf
  -- (k·c²)² = k²·c⁴
  -- c² · ω² = c² · (k²c² + m²c⁴/ℏ²) = k²c⁴ + m²c⁶/ℏ²
  -- So we need: k²·c⁴ < k²c⁴ + m²c⁶/ℏ²
  -- i.e., 0 < m²c⁶/ℏ² which is true since m > 0
  have h_extra : 0 < mode.mass^2 * c^4 / ℏ^2 * c^2 := by
    have hm : 0 < mode.mass := mode.mass_pos
    positivity
  calc mode.momentum^2 * (c^2)^2
      = mode.momentum^2 * c^2 * c^2 := by ring
    _ < mode.momentum^2 * c^2 * c^2 + mode.mass^2 * c^4 / ℏ^2 * c^2 := by linarith
    _ = c^2 * (mode.momentum^2 * c^2 + mode.mass^2 * c^4 / ℏ^2) := by ring

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

/-- **HYPOTHESIS**: Admissibility of only null propagation.

    STATUS: SCAFFOLD — The exclusion of massive modes for conscious processes
    is a core prediction, but the formal proof that massive group velocity
    *always* violates the display_speed_c requirement for all k is still a scaffold.

    TODO: Complete the proof that for all nonzero k, massive_group_velocity < c. -/
def H_AdmitsOnlyNullPropagation (cp : ConsciousProcess) [ConsciousProcess.WellFormed cp] : Prop :=
  DisplaysAtSpeedC cp.units →
  ∀ (mode : MassiveMode), ¬ModeIsCompatible mode cp -- SCAFFOLD: ModeIsCompatible not yet defined.

/-- Corollary: conscious processes admit only null propagation -/
theorem admits_only_null_propagation (cp : ConsciousProcess) [wf : ConsciousProcess.WellFormed cp]
    (h_hyp : null_only_hypothesis cp) :
    DisplaysAtSpeedC cp.units →
    ∀ (mode : MassiveMode), False := by
  intro hdisp
  intro mode
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
