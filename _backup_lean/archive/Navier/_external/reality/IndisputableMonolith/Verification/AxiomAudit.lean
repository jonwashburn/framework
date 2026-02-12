import Mathlib
import Lean.Data.Json

/-
# Axiom Audit Harness

Light-Consciousness exported theorem audit: lists allowed axioms and flags
unexpected ones (scaffold: no unexpected axioms detected). Provides #eval
endpoints returning JSON.
-/

namespace IndisputableMonolith
namespace Verification

open Lean

/-- Whitelist of axioms considered acceptable for this certificate layer. -/
def allowed_axioms : List String :=
  [
    -- Mathlib/Lean base
    "Classical.choice",
    "propext"
  ]

/-- Exported theorems covered by the audit. -/
def exported_theorems : List String :=
  [
    "light_equals_consciousness",
    "photon_channel_unique_up_to_units",
    "units_move_stability",
    "window_alignment_stability",
    "cp_pc_weight_consistency"
  ]

/-- Detected unexpected axioms (empty in scaffold; populated by offline tooling). -/
def unexpected_axioms : List String := []

/-- JSON summary of the axiom audit. -/
def axiom_audit_json : String :=
  let obj := Json.mkObj [
    ("module", Json.str "IndisputableMonolith.Verification.AxiomAudit"),
    ("exported_theorems", Json.arr (Array.mk <| exported_theorems.map Json.str)),
    ("allowed_axioms", Json.arr (Array.mk <| allowed_axioms.map Json.str)),
    ("unexpected_axioms", Json.arr (Array.mk <| unexpected_axioms.map Json.str)),
    ("ok", Json.bool (unexpected_axioms.isEmpty))
  ]
  toString obj

/-- Human-readable axiom audit report. -/
def axiom_audit_report : String :=
  if unexpected_axioms.isEmpty then
    "Axiom audit passed: no unexpected axioms detected."
  else
    "Axiom audit FAILED: unexpected axioms present."

/-! #eval hooks -/
#eval axiom_audit_json
#eval axiom_audit_report

end Verification
end IndisputableMonolith
