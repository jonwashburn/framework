import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Potential
import IndisputableMonolith.Causality.Basic

open Classical Function

namespace IndisputableMonolith.ClassicalBridge

open Potential Causality

variable {M : Recognition.RecognitionStructure}

/-- Elements reachable from a basepoint x0. -/
structure Component (M : Recognition.RecognitionStructure) (x0 : M.U) where
  y : M.U
  reachable : Reaches (Potential.Kin M) x0 y

/-- Restrict a potential to the reach component of x0. -/
def restrictToComponent (M : Recognition.RecognitionStructure) (x0 : M.U) (p : Potential.Pot M) :
  Component M x0 → ℤ :=
  fun c => p c.y

/-- The basepoint packaged as a component element. -/
def basepoint (x0 : M.U) : Component M x0 :=
  ⟨x0, ⟨0, ReachN.zero⟩⟩

/-- Potentials on components (functions from components to integers). -/
abbrev PotOnComp (M : Recognition.RecognitionStructure) (x0 : M.U) := Component M x0 → ℤ

/-- Gauge equivalence: two potentials on a component are equivalent if they differ by a constant. -/
def GaugeEq (M : Recognition.RecognitionStructure) (x0 : M.U) (f g : PotOnComp M x0) : Prop :=
  ∃ c : ℤ, ∀ yc, f yc = g yc + c

/-- Setoid for gauge equivalence. -/
def gaugeSetoid (M : Recognition.RecognitionStructure) (x0 : M.U) : Setoid (PotOnComp M x0) :=
{ r := GaugeEq (M:=M) x0
, iseqv :=
  ⟨ -- refl
    by
      intro f; refine ⟨(0 : ℤ), ?_⟩
      intro yc; simp
  , -- symm
    by
      intro f g h
      rcases h with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      intro yc
      have hfg := hc yc
      -- f yc = g yc + c ⇒ g yc = f yc + (-c)
      have := congrArg (fun z => z + (-c)) hfg
      -- rearrange
      simpa [add_comm, add_left_comm, add_assoc] using this.symm
  , -- trans
    by
      intro f g h hfg hgk
      rcases hfg with ⟨c₁, hc₁⟩; rcases hgk with ⟨c₂, hc₂⟩
      refine ⟨c₁ + c₂, ?_⟩
      intro yc
      have := hc₁ yc
      have := hc₂ yc
      -- f = g + c₁, g = h + c₂ ⇒ f = h + (c₁+c₂)
      simpa [add_comm, add_left_comm, add_assoc] using
        by
          have := congrArg (fun z => z + c₂) (hc₁ yc)
          simpa [add_comm, add_left_comm, add_assoc, hc₂ yc]
  ⟩ }

/-- Uniqueness of the additive constant in a gauge relation on a component. -/
lemma gauge_constant_unique {x0 : M.U} {f g : PotOnComp M x0}
  {c₁ c₂ : ℤ}
  (h₁ : ∀ yc, f yc = g yc + c₁)
  (h₂ : ∀ yc, f yc = g yc + c₂) : c₁ = c₂ := by
  -- Evaluate at the basepoint to identify the constant uniquely
  have hb1 := h₁ (basepoint (M:=M) x0)
  have hb2 := h₂ (basepoint (M:=M) x0)
  -- f x0 = g x0 + c₁ and f x0 = g x0 + c₂ ⇒ c₁ = c₂
  have := by
    have := congrArg (fun z => z - g (basepoint (M:=M) x0)) hb1
    have := congrArg (fun z => z - g (basepoint (M:=M) x0)) hb2
    -- but a simpler approach: rewrite both and compare
    skip
  -- Simpler: use add_left_cancel on integers
  have := by
    have h := hb1.trans hb2.symm
    -- g + c₁ = g + c₂ ⇒ c₁ = c₂
    simpa [add_comm, add_left_comm, add_assoc] using add_left_cancel (a:=g (basepoint (M:=M) x0)) (b:=c₁) (c:=c₂) h
  exact this

/-- Classical T4 restatement: for δ-potentials, there exists a unique constant
    such that the two restrictions differ by that constant on the reach component. -/
lemma T4_unique_constant_on_component
  {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) (x0 : M.U) :
  ∃! c : ℤ, ∀ yc : Component M x0, restrictToComponent (M:=M) x0 p yc =
                      restrictToComponent (M:=M) x0 q yc + c := by
  -- Existence from Potential.diff_const_on_component
  refine ⟨p x0 - q x0, ?_ , ?_⟩
  · intro yc
    have hconst := Potential.diff_const_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0)
      (y:=yc.y) yc.reachable
    -- p y - q y = p x0 - q x0 ⇒ p y = q y + (p x0 - q x0)
    simpa [restrictToComponent, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (eq_add_of_sub_eq hconst)
  · intro c hc
    -- Evaluate at basepoint to solve for c
    have hb := hc (basepoint (M:=M) x0)
    -- p x0 = q x0 + c ⇒ c = p x0 - q x0
    have : c = p x0 - q x0 := by
      -- rearrange by moving q x0 to the left
      have := congrArg (fun z => z - q x0) hb
      simpa [restrictToComponent, basepoint, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    simpa [this]

/-- Corollary: the gauge classes of any two δ-potentials coincide on the component. -/
lemma gaugeClass_const (x0 : M.U) {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 p) =
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 q) := by
  -- They differ by the constant (p x0 - q x0) on the component
  refine Quot.sound ?_;
  refine ⟨p x0 - q x0, ?_⟩
  intro yc
  have hconst := Potential.diff_const_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0)
    (y:=yc.y) yc.reachable
  simpa [restrictToComponent, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (eq_add_of_sub_eq hconst)

/-- Final classical correspondence (headline): for any δ, the space of δ-potentials
    on a reach component is a single gauge class ("defined up to a constant"). -/
theorem classical_T4_correspondence (x0 : M.U) {δ : ℤ}
  (p q : Potential.Pot M) (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  GaugeEq (M:=M) x0 (restrictToComponent (M:=M) x0 p) (restrictToComponent (M:=M) x0 q) := by
  -- directly produce the gauge witness using the unique-constant theorem
  rcases T4_unique_constant_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) (x0:=x0) hp hq with ⟨c, hc, _⟩
  exact ⟨c, hc⟩

end IndisputableMonolith.ClassicalBridge
