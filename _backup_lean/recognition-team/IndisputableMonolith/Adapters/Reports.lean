import IndisputableMonolith.RRF.Adapters.TraceTypes
import Lean.Data.Json

/-!
# RRF Adapters: Reports

Functions that generate RRF invariant reports from traces.

These reports are the connection between Lean proofs and empirical data.
-/


namespace IndisputableMonolith
namespace RRF.Adapters

open Lean (Json ToJson)

/-! ## Report Structures -/

/-- Result of checking an invariant. -/
structure InvariantCheck where
  /-- Name of the invariant. -/
  name : String
  /-- Did it pass? -/
  passed : Bool
  /-- Description of what was checked. -/
  description : String
  /-- Value (if applicable). -/
  value : Option Float
  deriving Repr

instance : ToJson InvariantCheck where
  toJson c := Json.mkObj [
    ("name", Json.str c.name),
    ("passed", Json.bool c.passed),
    ("description", Json.str c.description),
    ("value", match c.value with
      | some v => Json.num v.toUInt64.toNat
      | none => Json.null)
  ]

/-- A complete RRF invariant report. -/
structure RRFReport where
  /-- Trace identifier. -/
  traceId : String
  /-- All invariant checks. -/
  checks : List InvariantCheck
  /-- Overall pass/fail. -/
  allPassed : Bool
  /-- Summary statistics. -/
  summary : String
  deriving Repr

instance : ToJson RRFReport where
  toJson r := Json.mkObj [
    ("trace_id", Json.str r.traceId),
    ("checks", Json.arr (r.checks.map ToJson.toJson).toArray),
    ("all_passed", Json.bool r.allPassed),
    ("summary", Json.str r.summary)
  ]

/-! ## CPM Trace Checks -/

/-- Check energy decreasing trend. -/
def checkEnergyTrend (trace : CPMTrace) : InvariantCheck :=
  let passed := energyDecreasingTrend trace
  { name := "energy_decreasing"
  , passed := passed
  , description := "Energy should decrease over accepted moves"
  , value := none }

/-- Check balance phase acceptance rate. -/
def checkBalanceAcceptance (trace : CPMTrace) : InvariantCheck :=
  let passed := balanceHasLowerAcceptance trace
  let rate := acceptanceRateInPhase trace .balance
  { name := "balance_acceptance"
  , passed := passed
  , description := "Balance phase should have lower acceptance rate"
  , value := some rate }

/-- Check RMSD is reasonable (if available). -/
def checkRMSD (trace : CPMTrace) (threshold : Float := 10.0) : InvariantCheck :=
  match trace.finalRMSD with
  | none =>
    { name := "rmsd_check"
    , passed := true  -- Can't check without reference
    , description := "RMSD not available (no reference)"
    , value := none }
  | some rmsd =>
    { name := "rmsd_check"
    , passed := rmsd ≤ threshold
    , description := s!"RMSD should be ≤ {threshold} Å"
    , value := some rmsd }

/-- Generate full CPM report. -/
def generateCPMReport (trace : CPMTrace) (traceId : String) : RRFReport :=
  let checks := [
    checkEnergyTrend trace,
    checkBalanceAcceptance trace,
    checkRMSD trace
  ]
  let allPassed := checks.all (·.passed)
  { traceId := traceId
  , checks := checks
  , allPassed := allPassed
  , summary := if allPassed then "All checks passed" else "Some checks failed" }

/-! ## LNAL Trace Checks -/

/-- Check 8-tick cycle respect. -/
def checkEightTick (trace : LNALTrace) : InvariantCheck :=
  let passed := respectsEightTick trace
  { name := "eight_tick"
  , passed := passed
  , description := "All steps should respect 8-tick cycle"
  , value := none }

/-- Check J-cost is non-negative. -/
def checkJcostNonNeg (trace : LNALTrace) : InvariantCheck :=
  let passed := trace.steps.all (fun s => s.jcost ≥ 0.0)
  { name := "jcost_nonneg"
  , passed := passed
  , description := "J-cost should be non-negative"
  , value := none }

/-- Generate LNAL report. -/
def generateLNALReport (trace : LNALTrace) (traceId : String) : RRFReport :=
  let checks := [
    checkEightTick trace,
    checkJcostNonNeg trace
  ]
  let allPassed := checks.all (·.passed)
  { traceId := traceId
  , checks := checks
  , allPassed := allPassed
  , summary := if allPassed then "All LNAL checks passed" else "Some LNAL checks failed" }

/-! ## Sonification Report -/

/-- Check mean detune is reasonable. -/
def checkMeanDetune (trace : SonificationTrace) (threshold : Float := 50.0) : InvariantCheck :=
  let mad := meanAbsoluteDetune trace
  { name := "mean_detune"
  , passed := mad ≤ threshold
  , description := s!"Mean absolute detune should be ≤ {threshold} cents"
  , value := some mad }

/-- Generate sonification report. -/
def generateSonificationReport (trace : SonificationTrace) (traceId : String) : RRFReport :=
  let checks := [checkMeanDetune trace]
  let allPassed := checks.all (·.passed)
  { traceId := traceId
  , checks := checks
  , allPassed := allPassed
  , summary := if allPassed then "Sonification checks passed" else "Sonification checks failed" }

end RRF.Adapters
end IndisputableMonolith
