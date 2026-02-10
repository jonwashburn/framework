import Mathlib
import IndisputableMonolith.Verification
import IndisputableMonolith.Verification.Rendered

namespace IndisputableMonolith
namespace Verification

/-- Rendered falsifiability item tying a failure condition to a guarding lemma. -/
structure Falsifiable where
  id          : String
  wouldFailIf : String
  guardedBy   : String
deriving Repr

/-- List of falsifiability conditions with guarding lemmas. -/
@[simp] def falsifiabilityRendered : List Falsifiable :=
  [ { id := "KGateMismatch"
    , wouldFailIf := "K_A ≠ K_B"
    , guardedBy := "Verification.K_gate_bridge"
    }
  , { id := "ConeViolation"
    , wouldFailIf := "∃ n x y, rad y − rad x > c · (time y − time x)"
    , guardedBy := "Verification.cone_bound_export"
    }
  ]

/-- Machine-readable manifest: claims, gates, and knobs count. -/
structure RenderedManifest where
  claims         : List Rendered.RenderedClaim
  gates          : List Rendered.GateSpec
  falsifiability : List Falsifiable
  knobs          : Nat
deriving Repr

@[simp] def claimIds : List String := Rendered.dimlessClaimsRendered.map (fun c => c.id)
@[simp] def gateIds  : List String := Rendered.gatesRendered.map (fun g => g.id)

@[simp] def manifest : RenderedManifest :=
{ claims := Rendered.dimlessClaimsRendered
, gates  := Rendered.gatesRendered
, falsifiability := falsifiabilityRendered
, knobs  := knobsCount }

@[simp] def manifestStrings : List String :=
  [ "claims={" ++ String.intercalate ", " claimIds ++ "}"
  , "gates={"  ++ String.intercalate ", " gateIds  ++ "}"
  , "knobs="    ++ toString knobsCount ]

end Verification
end IndisputableMonolith
