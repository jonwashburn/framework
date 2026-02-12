import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.URCGenerators

/-(
Category ZeroParam: zero‑parameter admissible frameworks modulo units.
Objects carry: ledger, J, φ, 8‑tick, finite c. Morphisms preserve observables,
K‑gates, and J‑minimizers, and respect the units quotient.
-/

namespace IndisputableMonolith
namespace ZeroParam

open Foundation

/-- A zero‑parameter framework. -/
structure Framework where
  ledger : Type
  Jcost : ℝ → ℝ
  phi : ℝ
  /-- Dynamics: transformation on the ledger. -/
  dynamics : ledger → ledger
  /-- Eight-tick periodicity: the dynamics repeats every 8 ticks. -/
  eight_tick : ∀ s : ledger, dynamics s ≠ s ∧ (dynamics^[8]) s = s
  /-- Finite speed of information c. -/
  finite_c : ℝ
  finite_c_pos : 0 < finite_c
  inh : Nonempty ledger
  /-- Observables extracted from the ledger. -/
  observables : ledger → ℝ
  /-- K-gate transformation on the ledger. -/
  k_gate : ledger → ledger
  /-- Set of J-minimizing states. -/
  j_minimizers : Set ledger
  /-- Scaling factors (units). -/
  Units : Type
  /-- Identity unit. -/
  units_id : Units
  /-- Scale transformation. -/
  rescale : Units → ledger → ledger
  /-- Rescaling by identity is identity. -/
  rescale_id : rescale units_id = id
  /-- Scale invariance of observables. -/
  obs_invariant : ∀ u : Units, observables ∘ (rescale u) = observables



/-- Units quotient equivalence. -/
def morphismUpToUnits (F G : Framework) (f g : Morphism F G) : Prop :=
  ∃ (u : G.Units), f.map = (G.rescale u) ∘ g.map

/-- Admissibility of a zero‑parameter framework. -/
class Admissible (F : Framework) : Prop where
  (ledger_double_entry : ∀ x : F.ledger, F.observables x ≥ 0)
  (atomic_cost_J : ∀ r, F.Jcost r = 0 ↔ r = 1)
  (discrete_continuity : Continuous F.Jcost)
  (self_similarity_phi : F.phi = (1 + Real.sqrt 5) / 2)
  (eight_tick_3D : F.eight_tick)
  (finite_c : F.finite_c)
  (ledger_subsingleton : Subsingleton F.ledger)

/-- Morphisms preserve observables, K‑gates, and J‑minimizers. -/
structure Morphism (F G : Framework) where
  map : F.ledger → G.ledger
  preserves_observables : G.observables ∘ map = F.observables
  preserves_K_gate : map ∘ F.k_gate = G.k_gate ∘ map
  preserves_J_minimizers : ∀ x, x ∈ F.j_minimizers ↔ map x ∈ G.j_minimizers

/-- Identity morphism. -/
def id (F : Framework) : Morphism F F :=
  { map := id
  , preserves_observables := rfl
  , preserves_K_gate := rfl
  , preserves_J_minimizers := fun _ => Iff.rfl }

/-- Composition. -/
def comp {F G H : Framework} (g : Morphism G H) (f : Morphism F G) : Morphism F H :=
  { map := g.map ∘ f.map
  , preserves_observables := by
      simp only [Function.comp_assoc, g.preserves_observables, f.preserves_observables]
  , preserves_K_gate := by
      simp only [← Function.comp_assoc]
      rw [f.preserves_K_gate]
      simp only [Function.comp_assoc]
      rw [g.preserves_K_gate]
  , preserves_J_minimizers := fun x => by
      rw [f.preserves_J_minimizers, g.preserves_J_minimizers] }



/-- Left identity for morphisms. -/
theorem comp_id_left {F G : Framework} (f : Morphism F G) : comp (id G) f = f := by
  cases f; rfl

/-- Right identity for morphisms. -/
theorem comp_id_right {F G : Framework} (f : Morphism F G) : comp f (id F) = f := by
  cases f; rfl

/-- Associativity for morphisms. -/
theorem comp_assoc {F G H I : Framework}
  (h : Morphism H I) (g : Morphism G H) (f : Morphism F G) :
  comp h (comp g f) = comp (comp h g) f := by
  rfl

/-- A trivial morphism picking a default target ledger element. -/
noncomputable def trivialMorph (F G : Framework)
    (h_obs : G.observables ∘ (fun _ => G.inh.some) = F.observables)
    (h_kg : (fun _ => G.inh.some) ∘ F.k_gate = G.k_gate ∘ (fun _ => G.inh.some))
    (h_jm : ∀ x, x ∈ F.j_minimizers ↔ G.inh.some ∈ G.j_minimizers) : Morphism F G :=
  { map := fun _ => G.inh.some
  , preserves_observables := h_obs
  , preserves_K_gate := h_kg
  , preserves_J_minimizers := h_jm }

/-- Reflexivity of up-to-units equivalence. -/
theorem morphismUpToUnits_refl (F G : Framework) (f : Morphism F G) :
    morphismUpToUnits F G f f := by
  use G.units_id
  rw [G.rescale_id]
  simp only [Function.comp_id]


/-- Extensionality lemma: equality of maps implies equality of morphisms. -/
theorem morph_eq_of_map_eq {F G : Framework} {f g : Morphism F G}
  (hmap : f.map = g.map) : f = g := by
  cases f; cases g; simp at hmap; subst hmap
  congr
  · apply proof_irrel
  · apply proof_irrel
  · apply proof_irrel


end ZeroParam
end IndisputableMonolith
