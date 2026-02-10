import IndisputableMonolith.Fusion.ReactionNetworkRates
import IndisputableMonolith.Fusion.Ignition

/-!
# Reactivity Proxy ⟨σv⟩ (Concrete, Model Layer)

This module **commits** to a concrete analytic proxy for the thermally averaged reactivity:

`⟨σv⟩_proxy(T) := T · exp(-η(T))`

where `η(T)` is the simplified Gamow exponent from `Fusion.ReactionNetworkRates`.

## Why this proxy?

1. It is **explicit**, auditable, and smooth.
2. It preserves the core RS structure: RS coherence scales `η` by `S`, hence multiplies
   the exponent, giving a multiplicative enhancement in `exp(-η)`.
3. The extra prefactor `T` captures the qualitative fact that increasing temperature
   increases typical relative velocity and therefore increases reaction rate, not just tunneling.

This is still a proxy (not a Bosch–Hale fit). It is chosen because it enables
clean, fully formal bounding results in Lean that can later be tightened or replaced.
-/

namespace IndisputableMonolith
namespace Fusion
namespace ReactivityProxy

open ReactionNetworkRates
open Ignition
open NuclearBridge

noncomputable section
set_option autoImplicit false

/-! ## Definition -/

/-- Classical reactivity proxy: `⟨σv⟩(T) = T * exp(-η(T))`. -/
def sigmaV (g : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  g.temperature * classicalTunneling g cfgA cfgB

/-- RS reactivity proxy: `⟨σv⟩_RS(T) = T * exp(-η_RS(T))`. -/
def sigmaV_rs (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  g.temperature * rsTunneling c g cfgA cfgB

lemma sigmaV_nonneg (g : GamowParams) (cfgA cfgB : NuclearConfig) : 0 ≤ sigmaV g cfgA cfgB := by
  unfold sigmaV classicalTunneling
  have : 0 ≤ Real.exp (-gamowExponent g cfgA cfgB) := le_of_lt (Real.exp_pos _)
  have ht : 0 ≤ g.temperature := le_of_lt g.temperature_pos
  exact mul_nonneg ht this

lemma sigmaV_rs_nonneg (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    0 ≤ sigmaV_rs c g cfgA cfgB := by
  unfold sigmaV_rs rsTunneling rsTunnelingProbability
  have : 0 ≤ Real.exp (-rsGamowExponent c g cfgA cfgB) := le_of_lt (Real.exp_pos _)
  have ht : 0 ≤ g.temperature := le_of_lt g.temperature_pos
  exact mul_nonneg ht this

/-! ## RS monotone improvement (same T) -/

theorem sigmaV_rs_ge_sigmaV (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    sigmaV g cfgA cfgB ≤ sigmaV_rs c g cfgA cfgB := by
  unfold sigmaV sigmaV_rs
  -- Multiply the tunneling inequality by the positive temperature.
  have hprob : classicalTunneling g cfgA cfgB ≤ rsTunneling c g cfgA cfgB :=
    rsTunneling_ge_classical (c := c) (g := g) (cfgA := cfgA) (cfgB := cfgB)
  have ht : 0 ≤ g.temperature := le_of_lt g.temperature_pos
  exact mul_le_mul_of_nonneg_left hprob ht

end

end ReactivityProxy
end Fusion
end IndisputableMonolith
