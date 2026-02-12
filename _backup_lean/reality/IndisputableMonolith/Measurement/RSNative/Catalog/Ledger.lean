import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.Foundation.RecognitionOperator

/-!
# RS-Native Measurement Catalog: Ledger / Recognition

Concrete RS-native observables derived from `Foundation.LedgerState`.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Catalog
namespace Ledger

open IndisputableMonolith.Foundation

/-! ## Helper constructors -/

@[simp] def asCost (x : ℝ) : RSNative.Cost := ⟨x⟩
@[simp] def asSkew (x : ℝ) : RSNative.Skew := ⟨x⟩

/-! ## Protocols -/

def protocol_recognitionCost : Protocol :=
{ name := "ledger.recognition_cost"
, summary := "Sum of J-costs over active bonds in a single LedgerState (RS-native)."
, status := .derived
, assumptions := []
, falsifiers := []
}

def protocol_netSkew : Protocol :=
{ name := "ledger.net_skew"
, summary := "Net reciprocity skew σ = Σ log(x_e) over active bonds (should be 0 for admissible states)."
, status := .derived
, assumptions := []
, falsifiers := ["Find an admissible state with net_skew ≠ 0 (violates definition)."]
}

def protocol_reciprocitySkewAbs : Protocol :=
{ name := "ledger.reciprocity_skew_abs"
, summary := "Total absolute reciprocity skew Σ |log(x_e)| over active bonds."
, status := .derived
, assumptions := []
, falsifiers := []
}

def protocol_totalZ : Protocol :=
{ name := "ledger.total_Z"
, summary := "Total Z-invariant (integer) from `Z_patterns.sum`."
, status := .derived
, assumptions := []
, falsifiers := ["Find evolution step where total_Z changes despite `r_hat_conserves_patterns`."]
}

/-! ## Observables on a single ledger state -/

noncomputable def recognitionCost : Observable LedgerState RSNative.Cost :=
  fun s =>
  { value := asCost (RecognitionCost s)
  , window := some (Window.instant s.time)
  , protocol := protocol_recognitionCost
  }

noncomputable def netSkew : Observable LedgerState RSNative.Skew :=
  fun s =>
  { value := asSkew (net_skew s)
  , window := some (Window.instant s.time)
  , protocol := protocol_netSkew
  }

noncomputable def reciprocitySkewAbs : Observable LedgerState RSNative.Skew :=
  fun s =>
  { value := asSkew (reciprocity_skew_abs s)
  , window := some (Window.instant s.time)
  , protocol := protocol_reciprocitySkewAbs
  }

def totalZ : Observable LedgerState ℤ :=
  fun s =>
  { value := total_Z s
  , window := some (Window.instant s.time)
  , protocol := protocol_totalZ
  }

/-! ## Observables on traces -/

private def windowOfTrace (γ : List LedgerState) : Option Window :=
  match γ with
  | [] => none
  | s :: ss =>
    let t0 := s.time
    let tLast := (List.getLastD (s :: ss) s).time
    some ⟨t0, tLast - t0⟩

def protocol_pathAction : Protocol :=
{ name := "ledger.path_action"
, summary := "Discrete path action C[γ] = Σ RecognitionCost(s_t) over a trace (foldl)."
, status := .derived
, assumptions := ["Trace is ordered in time (for window metadata)."]
, falsifiers := []
}

noncomputable def pathAction : Observable (List LedgerState) RSNative.Cost :=
  fun γ =>
  { value := asCost (PathAction γ)
  , window := windowOfTrace γ
  , protocol := protocol_pathAction
  }

end Ledger
end Catalog
end RSNative
end Measurement
end IndisputableMonolith


