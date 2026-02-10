import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.Virtues.Wisdom
import IndisputableMonolith.Ethics.Virtues.Prudence

/-!
# RS-Native Measurement Catalog: Ethics / Skew

Observables on `Ethics.MoralState` and virtue operators like `WiseChoice` / `PrudentChoice`.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Catalog
namespace Ethics

open IndisputableMonolith.Ethics
open IndisputableMonolith.Ethics.Virtues

@[simp] def asSkew (x : ℝ) : RSNative.Skew := ⟨x⟩

def protocol_skew : Protocol :=
{ name := "ethics.skew"
, summary := "Agent skew (ledger reciprocity imbalance proxy) from MoralState."
, status := .derived
, assumptions := []
, falsifiers := []
}

def protocol_absSkew : Protocol :=
{ name := "ethics.abs_skew"
, summary := "Magnitude of skew |σ| (risk/imbalance magnitude)."
, status := .derived
, assumptions := []
, falsifiers := []
}

noncomputable def skew : Observable MoralState RSNative.Skew :=
  fun s =>
  { value := asSkew s.skew
  , window := none
  , protocol := protocol_skew
  }

noncomputable def absSkew : Observable MoralState RSNative.Skew :=
  fun s =>
  { value := asSkew (abs s.skew)
  , window := none
  , protocol := protocol_absSkew
  }

def protocol_wiseChoice : Protocol :=
{ name := "ethics.wise_choice"
, summary := "WiseChoice: selects option minimizing φ-discounted skew (definition in Wisdom.lean)."
, status := .derived
, assumptions := ["Choice list represents admissible alternatives."]
, falsifiers := []
}

def protocol_prudentChoice : Protocol :=
{ name := "ethics.prudent_choice"
, summary := "PrudentChoice: risk-adjusted minimization over {status quo} ∪ choices (definition in Prudence.lean)."
, status := .derived
, assumptions := ["λ is an externally chosen risk-aversion weight (policy, not core physics)."]
, falsifiers := []
}

noncomputable def wiseChoice (s : MoralState) : Observable (List MoralState) MoralState :=
  fun choices =>
  { value := WiseChoice s choices
  , window := none
  , protocol := protocol_wiseChoice
  }

noncomputable def prudentChoice (s : MoralState) (lambda : ℝ) : Observable (List MoralState) MoralState :=
  fun choices =>
  { value := PrudentChoice s choices lambda
  , window := none
  , protocol := protocol_prudentChoice
  , notes := ["If λ=0, Prudence reduces to min(|skew|) over {s}∪choices (see Prudence.lean)."]
  }

end Ethics
end Catalog
end RSNative
end Measurement
end IndisputableMonolith


