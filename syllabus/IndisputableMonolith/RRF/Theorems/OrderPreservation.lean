import IndisputableMonolith.RRF.Core.DisplayChannel
import IndisputableMonolith.RRF.Core.Strain
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# RRF Theorems: Order Preservation

Theorems about how ordering on states is preserved under various operations.

Key insight: RRF cares about *ordering* of states by strain, not absolute values.
Any operation that preserves this ordering preserves "meaning."

## Main Results

- `rank_invariant`: Monotone transforms preserve rank ordering
- `channel_transfer`: If channels are quality-equivalent, optimization transfers
-/


namespace IndisputableMonolith
namespace RRF.Theorems

variable {State : Type*}

/-! ## Rank Preservation -/

/-- The rank of a state x in a finite set S: number of states with lower J. -/
noncomputable def rank [Fintype State] [DecidableEq State]
    (J : State → ℝ) (x : State) : ℕ :=
  Finset.card { y ∈ Finset.univ | J y < J x }

/-- Strictly monotone transforms preserve strict ordering, hence ranks. -/
theorem strictMono_preserves_strict_order
    {J : State → ℝ} {g : ℝ → ℝ} (hg : StrictMono g)
    {x y : State} (hxy : J x < J y) :
    (g ∘ J) x < (g ∘ J) y :=
  hg hxy

/-- For finite state spaces, strictly monotone transforms preserve ranks. -/
theorem rank_invariant [Fintype State] [DecidableEq State]
    {J : State → ℝ} {g : ℝ → ℝ} (hg : StrictMono g) (x : State) :
    rank J x = rank (g ∘ J) x := by
  simp only [rank]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun h => hg h, fun h => hg.lt_iff_lt.mp h⟩

/-! ## Channel Transfer -/

open RRF.Core

/-- If two channels are quality-equivalent, their optimal states coincide. -/
theorem optimal_transfer {Obs₁ Obs₂ : Type*}
    {C₁ : DisplayChannel State Obs₁}
    {C₂ : DisplayChannel State Obs₂}
    (heq : QualityEquiv C₁ C₂)
    (x : State) :
    C₁.isOptimal x ↔ C₂.isOptimal x :=
  QualityEquiv.optimal_iff heq x

/-- If C₂.quality = g ∘ C₁.quality for monotone g, they induce the same order. -/
theorem channel_mono_transfer {Obs : Type*}
    {C₁ C₂ : DisplayChannel State Obs}
    {g : ℝ → ℝ} (hg : Monotone g)
    (hqual : ∀ o, C₂.quality o = g (C₁.quality o))
    (heq : C₁.observe = C₂.observe) :
    ∀ x y, C₁.stateQuality x ≤ C₁.stateQuality y →
           C₂.stateQuality x ≤ C₂.stateQuality y := by
  intro x y h
  simp only [DisplayChannel.stateQuality, Function.comp_apply] at *
  rw [← heq, hqual, hqual]
  exact hg h

/-! ## Strain Ordering Lemmas -/

/-- Strain ordering is transitive. -/
theorem strain_order_trans {S : StrainFunctional State}
    {x y z : State}
    (hxy : S.weaklyBetter x y) (hyz : S.weaklyBetter y z) :
    S.weaklyBetter x z :=
  le_trans hxy hyz

/-- Strict strain ordering is transitive. -/
theorem strain_strict_order_trans {S : StrainFunctional State}
    {x y z : State}
    (hxy : S.strictlyBetter x y) (hyz : S.strictlyBetter y z) :
    S.strictlyBetter x z :=
  lt_trans hxy hyz

/-- Equilibria are minimal elements. -/
theorem equilibria_minimal [StrainFunctional.NonNeg S]
    {x : State} (hx : S.isBalanced x) :
    S.isMinimizer x :=
  StrainFunctional.equilibria_are_minimizers x hx

end RRF.Theorems
end IndisputableMonolith
