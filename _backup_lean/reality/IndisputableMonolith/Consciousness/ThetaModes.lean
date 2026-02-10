import Mathlib
import IndisputableMonolith.Consciousness.GlobalPhase

/-!
# Θ Modes (Scaffold): global zero‑mode + local fluctuations

Your prose + `Source-Super.txt` talk about both:
- a shared global phase Θ, and
- local modulations / gradients.

To make those coexist cleanly, we introduce a decomposition:

  Θ_total(x,t) = Θ₀(t) + δθ(x,t)   (mod 1)

This file is a **scaffold**: it defines the objects and basic invariants so
downstream modules (no‑signaling, defects, transport) have a clean home.
-/

namespace IndisputableMonolith
namespace Consciousness
namespace ThetaModes

/-! ## Domain and fields -/

abbrev Spacetime := ℝ × ℝ × ℝ × ℝ

/-! Global mode Θ₀(t) lives in [0,1). -/
abbrev ThetaZeroMode := ℝ → UniversalPhase

/-! Local fluctuation δθ(x,t) is a real-valued field (later treated modulo 1). -/
abbrev ThetaFluctuation := Spacetime → ℝ

/-! Total phase in [0,1) via wrapping. -/
noncomputable def wrapPhase (x : ℝ) : ℝ := x - Int.floor x

lemma wrapPhase_bounds (x : ℝ) : 0 ≤ wrapPhase x ∧ wrapPhase x < 1 := by
  simp only [wrapPhase]
  constructor
  · have h := Int.floor_le x
    linarith
  · have h := Int.lt_floor_add_one x
    linarith

/-! ## Integer-shift invariance (mod 1) -/

lemma wrapPhase_add_int (x : ℝ) (z : ℤ) : wrapPhase (x + (z : ℝ)) = wrapPhase x := by
  unfold wrapPhase
  rw [Int.floor_add_intCast x z]
  simp

noncomputable def ThetaTotal (Θ0 : ThetaZeroMode) (δθ : ThetaFluctuation) (p : Spacetime) : UniversalPhase :=
  let t : ℝ := p.2.2.2
  let raw := (Θ0 t).val + δθ p
  ⟨wrapPhase raw, wrapPhase_bounds raw⟩

/-! ## Gauge equivalence (mod 1) -/

def phase_equiv (a b : ℝ) : Prop := wrapPhase a = wrapPhase b

theorem phase_equiv_refl (a : ℝ) : phase_equiv a a := by
  simp [phase_equiv]

/-! ## Sanity: pure-global case recovers the global phase -/

theorem thetaTotal_global_only (Θ0 : ThetaZeroMode) (p : Spacetime) :
    ThetaTotal Θ0 (fun _ => 0) p = ⟨wrapPhase (Θ0 p.2.2.2).val, wrapPhase_bounds (Θ0 p.2.2.2).val⟩ := by
  apply Subtype.ext
  simp [ThetaTotal]

end ThetaModes
end Consciousness
end IndisputableMonolith
