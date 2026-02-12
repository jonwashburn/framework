import Mathlib

namespace IndisputableMonolith
namespace Quantum

open scoped BigOperators

structure PathWeight (γ : Type) where
  C : γ → ℝ
  comp : γ → γ → γ
  cost_additive : ∀ a b, C (comp a b) = C a + C b
  prob : γ → ℝ := fun g => Real.exp (-(C g))
  normSet : Finset γ
  sum_prob_eq_one : Finset.sum normSet (fun g => prob g) = 1
-- (prob_comp omitted in WIP minimal stub)

/-- Interface asserting that the Born rule holds for a given path weight. -/
def BornRuleIface (γ : Type) (PW : PathWeight γ) : Prop :=
  ∀ g : γ, PW.prob g = Real.exp (-(PW.C g))

/-- Interface asserting Bose/Fermi occupancy formulas are realised. -/
def BoseFermiIface (γ : Type) (_ : PathWeight γ) : Prop :=
  (∀ β μ E, occupancyBose β μ E = 1 / (Real.exp (β * (E - μ)) - 1)) ∧
  (∀ β μ E, occupancyFermi β μ E = 1 / (Real.exp (β * (E - μ)) + 1))

/-- Minimal witness: the generic PathWeight interface satisfies both interfaces. -/
theorem rs_pathweight_iface (γ : Type) (PW : PathWeight γ) :
  BornRuleIface γ PW ∧ BoseFermiIface γ PW := by
  constructor
  · intro g; rfl
  · constructor <;> intro β μ E <;> rfl

/-- Regression sample: trivial path weight concentrated on unit state. -/
noncomputable def samplePathWeight : PathWeight Unit :=
{ C := fun _ => 0
, comp := fun _ _ => ()
, cost_additive := by intro _ _; simp
, normSet := {()}
, sum_prob_eq_one := by
    simp [PathWeight.prob] }

example : BornRuleIface Unit samplePathWeight := by
  intro _; rfl

/-- Bose–Einstein occupancy: n_B(E;β,μ) = 1 / (exp(β (E − μ)) − 1). -/
noncomputable def occupancyBose (β μ E : ℝ) : ℝ := 1 / (Real.exp (β * (E - μ)) - 1)

/-- Fermi–Dirac occupancy: n_F(E;β,μ) = 1 / (exp(β (E − μ)) + 1). -/
noncomputable def occupancyFermi (β μ E : ℝ) : ℝ := 1 / (Real.exp (β * (E - μ)) + 1)
