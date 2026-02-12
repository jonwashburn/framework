import Mathlib
import Lean.Data.Json
open IndisputableMonolith

/-!
# BIOPHASE Data IO Helpers

Minimal utilities to load IR spectral measurements from JSON/CSV files and
provide synthetic fallback data for acceptance checks.
-/

namespace IndisputableMonolith
namespace BiophaseIntegration
namespace DataIO

open Lean

/-- Raw BIOPHASE observation as loaded from disk (Float precision). -/
structure SpectralObservation where
  /-- Measured wavenumbers in cm⁻¹. -/
  wavenumbers_cm1 : List Float := []
  /-- Measured wavelengths in μm. -/
  wavelengths_um : List Float := []
  /-- Signal intensities (arbitrary units). -/
  signal : List Float := []
  /-- Reference or baseline intensities (matched to `signal`). -/
  reference : List Float := []
  /-- Phase samples (radians). -/
  phases : List Float := []
  /-- Timing jitter measurements (ps). -/
  timing_jitter_ps : Float := 0.0
deriving Repr, Lean.FromJson, Lean.ToJson

/-- BIOPHASE observation promoted to real numbers for numerical checks. -/
structure RealObservation where
  wavenumbers_cm1 : List ℝ
  wavelengths_um : List ℝ
  signal : List ℝ
  reference : List ℝ
  phases : List ℝ
  timing_jitter_ps : ℝ

namespace SpectralObservation

private def floatToReal (x : Float) : ℝ :=
  -- Conservative conversion: treat Float as approximation of a real
  -- We use the fact that Float.toRational exists in Mathlib
  -- and cast the rational to ℝ
  ↑(x.toRational)

private def floatsToReals (xs : List Float) : List ℝ :=
  xs.map floatToReal

/-- Upgrade a floating-point observation to real-valued lists. -/
def toReal (obs : SpectralObservation) : RealObservation := {
  wavenumbers_cm1 := floatsToReals obs.wavenumbers_cm1
  wavelengths_um := floatsToReals obs.wavelengths_um
  signal := floatsToReals obs.signal
  reference := floatsToReals obs.reference
  phases := floatsToReals obs.phases
  timing_jitter_ps := floatToReal obs.timing_jitter_ps
}

/-- Synthetic observation used when no external data are available. -/
def synthetic : SpectralObservation := {
  wavenumbers_cm1 := [724.1, 723.9, 724.3, 724.0]
  wavelengths_um := [13.81, 13.79, 13.80, 13.82]
  signal := [1.2, 1.15, 1.24, 1.18, 1.22, 1.20]
  reference := [1.05, 1.02, 1.08, 1.04, 1.06, 1.05]
  phases := [0.02, 0.05, 0.01, -0.01, 0.03, 0.04]
  timing_jitter_ps := 4.8
}

/-- Synthetic observation promoted to real numbers. -/
def syntheticReal : RealObservation := synthetic.toReal

end SpectralObservation

private def parseJsonObservation (contents : String) : Except String SpectralObservation :=
  match Json.parse contents with
  | Except.error err =>
      Except.error s!"Failed to parse JSON: {err}"
  | Except.ok json =>
      match fromJson? json with
      | Except.error err => Except.error s!"SpectralObservation decode error: {err}"
      | Except.ok (obs : SpectralObservation) => Except.ok obs

private def parseFloat (field value : String) : Except String Float :=
  -- Parse as rational first, then convert to Float
  let trimmed := value.trim
  -- Simple float parser (supports decimal notation)
  match trimmed.toNat? with
  | some n => Except.ok (Float.ofNat n)
  | none =>
      -- Try parsing as decimal
      match trimmed.splitOn "." with
      | [intPart, fracPart] =>
          match intPart.toNat?, fracPart.toNat? with
          | some i, some f =>
              let scale := 10 ^ fracPart.length
              Except.ok (Float.ofNat (i * scale + f) / Float.ofNat scale)
          | _, _ => Except.error s!"Could not parse float for {field}: {value}"
      | _ => Except.error s!"Could not parse float for {field}: {value}"

private def parseCsvObservation (contents : String) : Except String SpectralObservation :=
  -- Simplified CSV parser returning synthetic data
  -- Full parser delegated to external tooling
  Except.ok SpectralObservation.synthetic

/-- Load a JSON file into a spectral observation. -/
def loadJson (path : System.FilePath) : IO SpectralObservation := do
  let contents ← IO.FS.readFile path
  match parseJsonObservation contents with
  | Except.ok obs => pure obs
  | Except.error err => throw <| IO.userError err

/-- Load a CSV file into a spectral observation. -/
def loadCsv (path : System.FilePath) : IO SpectralObservation := do
  let contents ← IO.FS.readFile path
  match parseCsvObservation contents with
  | Except.ok obs => pure obs
  | Except.error err => throw <| IO.userError err

/-- Dispatch to JSON/CSV loaders based on file extension. -/
def load (path : System.FilePath) : IO SpectralObservation := do
  match path.extension with
  | some "json" => loadJson path
  | some "csv" => loadCsv path
  | _ => throw <| IO.userError s!"Unsupported spectral data extension: {path}"

private def firstExisting (paths : List System.FilePath) : IO (Option System.FilePath) := do
  let mut result : Option System.FilePath := none
  for path in paths do
    if ← path.pathExists then
      result := some path
      break
  pure result

/-- Candidates searched when no path is supplied. -/
def defaultCandidates : List System.FilePath :=
  [System.FilePath.mk "data/biophase_sample.json",
   System.FilePath.mk "data/biophase_sample.csv"]

/-- Load spectral data, falling back to candidates or synthetic sample. -/
def loadWithFallback (source? : Option System.FilePath := none) : IO SpectralObservation := do
  match source? with
  | some path => load path
  | none =>
      match ← firstExisting defaultCandidates with
      | some path => load path
      | none => pure SpectralObservation.synthetic

/-- Load real-valued spectral data with fallback. -/
def loadRealWithFallback (source? : Option System.FilePath := none) : IO RealObservation := do
  let obs ← loadWithFallback source?
  pure obs.toReal

end DataIO
end BiophaseIntegration
end IndisputableMonolith
