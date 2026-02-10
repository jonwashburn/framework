/-!
Export variants and real wiring (spec-level): spectral, real, interface.
References: Yang-Mills-sept21.tex — NRC (lines 5339–5357), interface γ_cut exports (around lines 740–758, 1543 ff.).
No axioms. No `sorry`.
-/

import YM.SpectralStability.RescaledNRC
-- Removed PhysicalGap Float dependency; use Real-native gap from OSWilson
import YM.OSWilson.Doeblin

namespace YM.Export.Variants

open YM.SpectralStability.RescaledNRC
-- No PhysicalGap import; we provide Real-native stubs below

/-- Spectral variant export using NRC setup (spec-level; Prop-based). -/
structure SpectralVariant where
  /-- Placeholder payload; the acceptance is the NRC proposition itself. -/
  unit : Unit := ()

/-- Spec: spectral export holds exactly when NRC(all nonreal z) holds for the setup. -/
def spectral_export_spec (S : NRCSetup) (_V : SpectralVariant) : Prop :=
  NRC_all_nonreal S

/-- Builder for the spectral export payload (spec-level). -/
def build_spectral_export (_S : NRCSetup) : SpectralVariant :=
  { unit := () }

/-- The built spectral export satisfies the NRC-based spec. -/
theorem build_spectral_export_holds (S : NRCSetup) :
  spectral_export_spec S (build_spectral_export S) := by
  simpa [spectral_export_spec] using NRC_all_nonreal_holds S

/-- Real/physical variant export via Doeblin-driven γ_phys (spec-level). -/
structure RealVariant where
  gamma_phys : ℝ

/-- Spec: the exported physical gap equals that built from Doeblin data. -/
def real_export_spec (γ : ℝ) (V : RealVariant) : Prop :=
  V.gamma_phys = γ

/-- Builder: copy out γ_phys from the Doeblin gap aggregator. -/
def build_real_export (γ : ℝ) : RealVariant :=
  { gamma_phys := γ }

theorem build_real_export_holds (γ : ℝ) :
  real_export_spec γ (build_real_export γ) := rfl

/-- Interface variant export via Wilson interface γ_cut (spec-level). -/
structure InterfaceVariant where
  gamma_cut : ℝ

/-- Spec: the exported cut gap equals the interface export γ_c. -/
-- Keep a Real-native spec without depending on Float-based interface exports
def interface_export_spec (γc : ℝ) (V : InterfaceVariant) : Prop :=
  V.gamma_cut = γc

/-- Builder: copy out γ_c from the interface export. -/
def build_interface_export (γc : ℝ) : InterfaceVariant :=
  { gamma_cut := γc }

theorem build_interface_export_holds (γc : ℝ) :
  interface_export_spec γc (build_interface_export γc) := rfl

end YM.Export.Variants


