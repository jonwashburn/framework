import Mathlib
import IndisputableMonolith.OctaveKernel.Basic

namespace IndisputableMonolith
namespace OctaveKernel

/-!
# OctaveKernel.Invariance

High-signal “RRF-style” invariance lemmas for the Octave kernel.

These are *pure mathematics*: they do **not** claim anything empirical.

Main idea:
- If you reparameterize a cost/quality scale by a **strictly monotone** function,
  you do not change the **ranking** of states, nor the **argmin** set.

This is the precise mathematical backbone for safe statements like:
“Any strictly monotone surrogate metric preserves which states are optimal.”
-/

/-! ## ArgMin (set of global minimizers) -/

/-- The (global) argmin set of a cost functional. -/
def ArgMin {α : Type} (f : α → ℝ) : Set α :=
  { x | ∀ y, f x ≤ f y }

namespace ArgMin

@[simp] lemma mem_def {α : Type} {f : α → ℝ} {x : α} :
    x ∈ ArgMin f ↔ ∀ y, f x ≤ f y := Iff.rfl

end ArgMin

/-! ## Ranking invariance under StrictMono reparameterizations -/

theorem strictMono_preserves_le {α : Type} {f : α → ℝ} {g : ℝ → ℝ}
    (hg : StrictMono g) (x y : α) :
    g (f x) ≤ g (f y) ↔ f x ≤ f y := by
  -- `StrictMono.le_iff_le` is the standard “order embedding” lemma.
  simpa using (hg.le_iff_le)

theorem strictMono_preserves_lt {α : Type} {f : α → ℝ} {g : ℝ → ℝ}
    (hg : StrictMono g) (x y : α) :
    g (f x) < g (f y) ↔ f x < f y := by
  simpa using (hg.lt_iff_lt)

/-! ## ArgMin invariance -/

theorem argMin_comp_strictMono {α : Type} {f : α → ℝ} {g : ℝ → ℝ}
    (hg : StrictMono g) :
    ArgMin (fun x => g (f x)) = ArgMin f := by
  ext x
  constructor
  · intro hx y
    -- hx : ∀ y, g(f x) ≤ g(f y)
    have hxy : g (f x) ≤ g (f y) := hx y
    -- pull back through strict monotonicity
    exact (strictMono_preserves_le (f := f) hg x y).1 hxy
  · intro hx y
    -- push forward via monotonicity
    exact hg.monotone (hx y)

/-! ## Channel helper: if a channel's quality is a strict-monotone transform of cost -/

theorem argMin_channel_eq_cost {L : Layer} (C : Channel L) (g : ℝ → ℝ)
    (hg : StrictMono g)
    (h : ∀ s : L.State, Channel.stateQuality C s = g (L.cost s)) :
    ArgMin (Channel.stateQuality C) = ArgMin L.cost := by
  -- Reduce to the generic argmin invariance lemma.
  have : (fun s => Channel.stateQuality C s) = fun s => g (L.cost s) := by
    funext s; exact h s
  -- Rewrite, then apply `argMin_comp_strictMono`.
  simpa [this] using (argMin_comp_strictMono (f := L.cost) hg)

/-! ## Affine invariance (special case of StrictMono) -/

/-- Affine transforms with positive slope are strictly monotone. -/
lemma affine_strictMono {a b : ℝ} (ha : 0 < a) : StrictMono (fun x => a * x + b) := by
  intro x y hxy
  have : a * x < a * y := mul_lt_mul_of_pos_left hxy ha
  linarith

/-- Affine reparameterization preserves argmin. -/
theorem argMin_affine_invariant {α : Type} {f : α → ℝ} {a b : ℝ} (ha : 0 < a) :
    ArgMin (fun x => a * f x + b) = ArgMin f :=
  argMin_comp_strictMono (affine_strictMono ha)

/-! ## Composition of StrictMono -/

/-- Composition of strictly monotone functions is strictly monotone. -/
lemma strictMono_comp {g h : ℝ → ℝ} (hg : StrictMono g) (hh : StrictMono h) :
    StrictMono (g ∘ h) := hg.comp hh

/-- Iterated reparameterization preserves argmin. -/
theorem argMin_comp_strictMono_comp {α : Type} {f : α → ℝ} {g h : ℝ → ℝ}
    (hg : StrictMono g) (hh : StrictMono h) :
    ArgMin (fun x => g (h (f x))) = ArgMin f := by
  have : ArgMin (fun x => g (h (f x))) = ArgMin (fun x => h (f x)) :=
    argMin_comp_strictMono hg
  rw [this]
  exact argMin_comp_strictMono hh

/-! ## Multiple channels measuring the same underlying cost -/

/-- Two channels with quality as strictly-monotone transforms of the same cost
    have identical argmin sets. This is the key lemma for "display invariance". -/
theorem two_channels_same_argmin {L : Layer}
    (C₁ C₂ : Channel L) (g₁ g₂ : ℝ → ℝ)
    (hg₁ : StrictMono g₁) (hg₂ : StrictMono g₂)
    (h₁ : ∀ s, Channel.stateQuality C₁ s = g₁ (L.cost s))
    (h₂ : ∀ s, Channel.stateQuality C₂ s = g₂ (L.cost s)) :
    ArgMin (Channel.stateQuality C₁) = ArgMin (Channel.stateQuality C₂) := by
  rw [argMin_channel_eq_cost C₁ g₁ hg₁ h₁]
  rw [argMin_channel_eq_cost C₂ g₂ hg₂ h₂]

/-! ## Ranking equivalence -/

/-- Two functions have the same ranking if they agree on all pairwise comparisons. -/
def SameRanking {α : Type} (f g : α → ℝ) : Prop :=
  ∀ x y, f x ≤ f y ↔ g x ≤ g y

namespace SameRanking

lemma refl {α : Type} (f : α → ℝ) : SameRanking f f :=
  fun _ _ => Iff.rfl

lemma symm {α : Type} {f g : α → ℝ} (h : SameRanking f g) : SameRanking g f :=
  fun x y => (h x y).symm

lemma trans {α : Type} {f g h : α → ℝ}
    (hfg : SameRanking f g) (hgh : SameRanking g h) : SameRanking f h :=
  fun x y => (hfg x y).trans (hgh x y)

/-- StrictMono reparameterization preserves ranking. -/
lemma of_strictMono {α : Type} {f : α → ℝ} {g : ℝ → ℝ} (hg : StrictMono g) :
    SameRanking f (fun x => g (f x)) := by
  intro x y
  exact (strictMono_preserves_le hg x y).symm

end SameRanking

/-- Functions with the same ranking have the same argmin. -/
theorem argMin_of_sameRanking {α : Type} {f g : α → ℝ} (h : SameRanking f g) :
    ArgMin f = ArgMin g := by
  ext x
  constructor
  · intro hx y
    exact (h x y).1 (hx y)
  · intro hx y
    exact (h x y).2 (hx y)

/-! ## Epsilon-optimal sets -/

/-- The set of ε-optimal states (within ε of the minimum value). -/
def EpsOptimal {α : Type} (f : α → ℝ) (ε : ℝ) : Set α :=
  { x | ∀ y, f x ≤ f y + ε }

/-- ArgMin is the intersection of all EpsOptimal sets for ε > 0. -/
theorem argMin_eq_iInter_epsOptimal {α : Type} (f : α → ℝ) :
    ArgMin f = ⋂ (ε : ℝ) (_ : 0 < ε), EpsOptimal f ε := by
  ext x
  simp only [ArgMin, EpsOptimal, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hx ε _ y
    have := hx y
    linarith
  · intro hx y
    -- For any ε > 0, f x ≤ f y + ε. Taking ε → 0, we get f x ≤ f y.
    by_contra h
    push_neg at h
    -- h : f y < f x, so f x - f y > 0
    have hε : 0 < f x - f y := by linarith
    have := hx (f x - f y) hε y
    -- this gives f x ≤ f y + (f x - f y) = f x, which is fine
    -- but we had f y < f x, so f x ≤ f y + (f x - f y) = f x
    -- This is not a contradiction directly. Let me fix the proof.
    -- Actually, use ε = (f x - f y) / 2
    have hε2 : 0 < (f x - f y) / 2 := by linarith
    have h2 := hx ((f x - f y) / 2) hε2 y
    -- h2 : f x ≤ f y + (f x - f y) / 2
    linarith

/-! ## Cost-preserving mappings -/

/-- A cost-preserving map between layer state spaces. -/
def CostPreserving {L₁ L₂ : Layer} (f : L₁.State → L₂.State) : Prop :=
  ∀ s, L₂.cost (f s) = L₁.cost s

/-- Cost-preserving maps preserve argmin. -/
theorem argMin_of_costPreserving {L₁ L₂ : Layer} (f : L₁.State → L₂.State)
    (hCost : CostPreserving f) (hSurj : Function.Surjective f) :
    ∀ s₁ ∈ ArgMin L₁.cost, f s₁ ∈ ArgMin L₂.cost := by
  intro s₁ hs₁ s₂
  obtain ⟨t, ht⟩ := hSurj s₂
  rw [← ht, hCost t, hCost s₁]
  exact hs₁ t

/-- If f is bijective and cost-preserving, argmin sets correspond exactly. -/
theorem argMin_equiv_of_costPreserving {L₁ L₂ : Layer} (e : L₁.State ≃ L₂.State)
    (hCost : CostPreserving e) :
    ArgMin L₂.cost = e '' ArgMin L₁.cost := by
  ext s₂
  constructor
  · intro hs₂
    refine ⟨e.symm s₂, ?_, e.apply_symm_apply s₂⟩
    intro t
    -- hs₂ : ∀ t', L₂.cost s₂ ≤ L₂.cost t'
    -- We need: L₁.cost (e.symm s₂) ≤ L₁.cost t
    have h1 := hs₂ (e t)
    -- h1 : L₂.cost s₂ ≤ L₂.cost (e t)
    -- Using cost preservation: L₂.cost (e t) = L₁.cost t
    rw [hCost t] at h1
    -- Also: s₂ = e (e.symm s₂), so L₂.cost s₂ = L₂.cost (e (e.symm s₂)) = L₁.cost (e.symm s₂)
    have h2 : L₂.cost s₂ = L₁.cost (e.symm s₂) := by
      conv_lhs => rw [← e.apply_symm_apply s₂]
      exact hCost (e.symm s₂)
    rw [h2] at h1
    exact h1
  · intro ⟨s₁, hs₁, heq⟩
    rw [← heq]
    intro t
    obtain ⟨u, hu⟩ := e.surjective t
    rw [← hu, hCost s₁, hCost u]
    exact hs₁ u

/-! ## Monotone cost transforms across layers -/

/-- A layer map is cost-monotone if it preserves cost ordering. -/
def CostMonotone {L₁ L₂ : Layer} (f : L₁.State → L₂.State) : Prop :=
  ∀ s t, L₁.cost s ≤ L₁.cost t → L₂.cost (f s) ≤ L₂.cost (f t)

/-- Strictly monotone cost relationship. -/
def CostStrictMono {L₁ L₂ : Layer} (f : L₁.State → L₂.State) : Prop :=
  ∀ s t, L₁.cost s < L₁.cost t → L₂.cost (f s) < L₂.cost (f t)

/-- Strict cost monotonicity implies argmin preservation for surjective maps. -/
theorem argMin_of_costStrictMono {L₁ L₂ : Layer} (f : L₁.State → L₂.State)
    (hMono : CostStrictMono f) (hSurj : Function.Surjective f) :
    ∀ s ∈ ArgMin L₂.cost, ∃ t ∈ ArgMin L₁.cost, f t = s := by
  intro s₂ hs₂
  obtain ⟨s₁, rfl⟩ := hSurj s₂
  refine ⟨s₁, ?_, rfl⟩
  intro t
  -- We show L₁.cost s₁ ≤ L₁.cost t by contradiction.
  by_contra h
  push_neg at h
  -- If L₁.cost t < L₁.cost s₁, then by strict monotonicity
  -- L₂.cost (f t) < L₂.cost (f s₁), contradicting s₂ = f s₁ ∈ ArgMin L₂.cost.
  have := hMono t s₁ h
  have hs₂_min := hs₂ (f t)
  linarith

end OctaveKernel
end IndisputableMonolith
