import Hodge.Analytic.Forms
import Mathlib.Topology.Algebra.Support

/-!
# Stage 1: Test forms (compactly supported smooth forms)

This module begins the “Track A / Stage 1” refactor from `tex/archive/HodgePlan-mc-28.1.26.rtf`:
we introduce **compactly supported smooth k-forms** as the test object for currents.

**Scope (initial)**: this file only defines the type of test forms and basic algebraic operations
(0, +, scalar multiplication) together with compact-support closure lemmas.

**Not yet implemented (Stage 1A/1B)**:
- LF / Fréchet topology on test forms
- continuity of `d`, `⋏`, pullback on the LF space
- definition of currents as `ContinuousLinearMap` out of test forms
-/

noncomputable section

open Classical

namespace Hodge

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  {k : ℕ}

/-- The type of **test k-forms**: smooth k-forms with compact support. -/
abbrev TestForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] :=
  { ω : SmoothForm n X k // HasCompactSupport ω.as_alternating }

namespace TestForm

-- Convenience coercion
instance : CoeTC (TestForm n X k) (SmoothForm n X k) where
  coe ω := ω.1

@[simp] theorem coe_mk (ω : SmoothForm n X k) (h : HasCompactSupport ω.as_alternating) :
    ((⟨ω, h⟩ : TestForm n X k) : SmoothForm n X k) = ω := rfl

@[simp] theorem hasCompactSupport (ω : TestForm n X k) : HasCompactSupport ω.1.as_alternating :=
  ω.2

/-! ## Basic algebraic operations -/

instance : Zero (TestForm n X k) :=
  ⟨⟨0, by
    -- `as_alternating` of the zero form is the zero function
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : X => (0 : FiberAlt n k)))⟩⟩

@[simp] theorem coe_zero : ((0 : TestForm n X k) : SmoothForm n X k) = 0 := rfl

instance : Add (TestForm n X k) :=
  ⟨fun ω η =>
    ⟨ω.1 + η.1, by
      -- compact support is closed under addition
      simpa using (HasCompactSupport.add ω.2 η.2)⟩⟩

@[simp] theorem coe_add (ω η : TestForm n X k) :
    ((ω + η : TestForm n X k) : SmoothForm n X k) = (ω : SmoothForm n X k) + η := rfl

instance : Neg (TestForm n X k) :=
  ⟨fun ω =>
    ⟨-ω.1, by
      simpa using (HasCompactSupport.neg ω.2)⟩⟩

@[simp] theorem coe_neg (ω : TestForm n X k) :
    ((-ω : TestForm n X k) : SmoothForm n X k) = -(ω : SmoothForm n X k) := rfl

instance : Sub (TestForm n X k) :=
  ⟨fun ω η => ω + (-η)⟩

@[simp] theorem coe_sub (ω η : TestForm n X k) :
    ((ω - η : TestForm n X k) : SmoothForm n X k) = (ω : SmoothForm n X k) - η := rfl

instance : SMul ℂ (TestForm n X k) :=
  ⟨fun c ω =>
    ⟨c • ω.1, by
      -- constant scalar multiplication preserves compact support
      -- Use `HasCompactSupport.comp_left` (avoids heavier typeclass inference than `smul_left`).
      have h :
          HasCompactSupport ((fun y : FiberAlt n k => c • y) ∘ ω.1.as_alternating) :=
        HasCompactSupport.comp_left ω.2 (by
          -- goal: (fun y => c • y) 0 = 0, proved by extensionality
          ext v
          simp)
      simpa [Function.comp] using h⟩⟩

@[simp] theorem coe_smul (c : ℂ) (ω : TestForm n X k) :
    ((c • ω : TestForm n X k) : SmoothForm n X k) = c • (ω : SmoothForm n X k) := rfl

/-! ## TODO (Stage 1): LF topology and continuity -/

-- TODO: define the LF topology on `TestForm n X k`
-- TODO: prove continuity of `smoothExtDeriv` on test forms
-- TODO: prove continuity of wedge product on test forms

end TestForm

end Hodge

end
