import Mathlib

/-!
# BIOPHASE Acceptance Specifications

Shared definitions for the BIOPHASE interface specification and acceptance criteria.
This module acts as the source of truth for what constitutes a "BIOPHASE-compatible"
channel, breaking the dependency cycle between `BiophasePhysics` (which calculates
feasibility) and `Consciousness` (which uses the result for theorems).

## Key Components
- `BiophaseSpec`: The physical parameters of the interface (λ₀, E_rec, etc.).
- `ChannelType`: The types of physical channels considered (EM, Gravitational, Neutrino).
- `PassesBiophase`: The predicate defining whether a channel meets the spec.
-/

namespace IndisputableMonolith
namespace BiophaseCore

/-- BIOPHASE specification parameters -/
structure BiophaseSpec where
  /-- IR wavelength (μm) -/
  lambda0 : ℝ
  /-- Recognition energy (eV) -/
  E_rec : ℝ
  /-- Gating/coherence time window (ps) -/
  tau_gate : ℝ
  /-- Spectral reference (cm⁻¹) -/
  nu0_cm1 : ℝ

  /-- Acceptance: correlation threshold -/
  rho_min : ℝ
  /-- Acceptance: SNR threshold -/
  snr_min : ℝ
  /-- Acceptance: circular variance threshold -/
  circ_var_max : ℝ

  /-- Constraints from spec -/
  lambda0_spec : lambda0 = 13.8
  E_rec_spec : E_rec = 0.090  -- φ⁻⁵ eV ≈ 0.090
  tau_gate_spec : tau_gate = 65
  nu0_spec : nu0_cm1 = 724
  rho_spec : rho_min = 0.30
  snr_spec : snr_min = 5.0
  circ_var_spec : circ_var_max = 0.40

/-- Standard BIOPHASE specification from Source.txt -/
def StandardBiophase : BiophaseSpec where
  lambda0 := 13.8
  E_rec := 0.090
  tau_gate := 65
  nu0_cm1 := 724
  rho_min := 0.30
  snr_min := 5.0
  circ_var_max := 0.40
  lambda0_spec := rfl
  E_rec_spec := rfl
  tau_gate_spec := rfl
  nu0_spec := rfl
  rho_spec := rfl
  snr_spec := rfl
  circ_var_spec := rfl

/-- Channel types at the physical level -/
inductive ChannelType
  | Electromagnetic  -- Photons, EM field
  | Gravitational    -- Gravitons, metric perturbations
  | Neutrino         -- Weakly interacting fermions
  | Other            -- Hypothetical or composite
  deriving DecidableEq, Repr

/-- A channel passes BIOPHASE acceptance criteria -/
def PassesBiophase (spec : BiophaseSpec) (channel : ChannelType) : Prop :=
  ∃ (ρ snr circ_var : ℝ),
    ρ ≥ spec.rho_min ∧
    snr ≥ spec.snr_min ∧
    circ_var ≤ spec.circ_var_max

end BiophaseCore
end IndisputableMonolith
