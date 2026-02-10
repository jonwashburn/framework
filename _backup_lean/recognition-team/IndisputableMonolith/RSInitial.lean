import Mathlib
import IndisputableMonolith.ZeroParam
import IndisputableMonolith.Foundation.RecognitionOperator

/-(
RS as initial object in ZeroParam (scaffold).

Provides the RS object and a unique morphism existence/uniqueness axiom
capturing the initiality property; factorization lemmas would connect the
ledger/J/φ/eight‑tick components in future detailed developments.
-/

namespace IndisputableMonolith
namespace RSInitial

open ZeroParam

/-- Hypothesis: RS units action is invariant. -/
def rs_units_invariant_hypothesis : Prop :=
  ∀ (s : ℝ) (l : Foundation.LedgerState),
    IndisputableMonolith.Cost.Jcost (Foundation.reciprocity_skew { l with bond_multipliers := fun b => s * l.bond_multipliers b }) =
      IndisputableMonolith.Cost.Jcost (Foundation.reciprocity_skew l) ∧
    Foundation.reciprocity_skew { l with bond_multipliers := fun b => s * l.bond_multipliers b } =
      Foundation.reciprocity_skew l

/-- The RS framework object. -/
def RS (h_inv : rs_units_invariant_hypothesis)
       (dyn : Foundation.LedgerState → Foundation.LedgerState)
       (h_8tick : ∀ s, dyn s ≠ s ∧ (dyn^[8]) s = s) : Framework :=
  { ledger := Foundation.LedgerState
  , Jcost := IndisputableMonolith.Cost.Jcost
  , phi := IndisputableMonolith.Constants.phi
  , dynamics := dyn
  , eight_tick := h_8tick


  , finite_c := (299792458 : ℝ)
  , finite_c_pos := by norm_num
  , inh := ⟨{ channels := fun _ => 0, Z_patterns := [], global_phase := 0, time := 0
            , active_bonds := ∅, bond_multipliers := fun _ => 1, bond_pos := fun h => by nomatch h
            , bond_agents := fun _ => none }⟩
  , observables := Foundation.reciprocity_skew
  , k_gate := id  -- Simplified for scaffold
  , j_minimizers := { s | Foundation.RecognitionCost s = 0 }
  , Units := ℝ
  , units_id := 1
  , rescale := fun s l => { l with bond_multipliers := fun b => s * l.bond_multipliers b }
  , rescale_id := by
      funext l
      simp only [id_eq]
      cases l; simp only [one_mul]
  , obs_invariant := by
      intro s
      funext l
      simp only [Function.comp_apply]
      exact (h_inv s l).2 }



/-- Hypothesis: RS admissibility properties. -/
structure RSAdmissibleHypotheses (h_inv : rs_units_invariant_hypothesis) : Prop where
  atomic_cost_J : ∀ r, (RS h_inv).Jcost r = 0 ↔ r = 1
  discrete_continuity : Continuous (RS h_inv).Jcost
  ledger_subsingleton : Subsingleton (RS h_inv).ledger

/-- RS is admissible. -/
instance (h_inv : rs_units_invariant_hypothesis) (h_adm : RSAdmissibleHypotheses h_inv) :
    ZeroParam.Admissible (RS h_inv) :=
  { ledger_double_entry := fun x => Foundation.reciprocity_skew_nonneg x
  , atomic_cost_J := h_adm.atomic_cost_J
  , discrete_continuity := h_adm.discrete_continuity
  , self_similarity_phi := rfl
  , eight_tick_3D := by
      unfold RS
      simp
  , finite_c := by
      unfold RS
      simp
  , units_quotient := { respects_units := fun x => ⟨1, by rfl⟩ }
  , ledger_subsingleton := h_adm.ledger_subsingleton }


/-- Constructive initial morphism skeleton. -/
noncomputable def initial_morphism (h_inv : rs_units_invariant_hypothesis) (G : Framework)
    (h_obs : ∀ x, G.observables G.inh.some = Foundation.reciprocity_skew x)
    (h_kg : ∀ x, G.k_gate G.inh.some = G.inh.some)
    (h_jm : ∀ x, x ∈ (RS h_inv).j_minimizers ↔ G.inh.some ∈ G.j_minimizers)
    (h_units : ∀ u : (RS h_inv).UnitsGroup, G.UnitsAction (G.units_map_const) G.inh.some = G.inh.some) :
    Morphism (RS h_inv) G :=
  ZeroParam.trivialMorph (RS h_inv) G h_obs h_kg h_jm h_units

/-- Hypothesis: Uniqueness of initial morphism up to units. -/
def initial_morphism_unique_up_to_units_hypothesis
    (h_inv : rs_units_invariant_hypothesis) (G : Framework) (f : ZeroParam.Morphism (RS h_inv) G)
    (h_m_obs : ∀ x, G.observables G.inh.some = Foundation.reciprocity_skew x)
    (h_m_kg : ∀ x, G.k_gate G.inh.some = G.inh.some)
    (h_m_jm : ∀ x, x ∈ (RS h_inv).j_minimizers ↔ G.inh.some ∈ G.j_minimizers)
    (h_m_units : ∀ u : (RS h_inv).UnitsGroup, G.UnitsAction (G.units_map_const) G.inh.some = G.inh.some) : Prop :=
  ∀ x, ∃ u : G.UnitsGroup, f.map x = G.UnitsAction u ((initial_morphism h_inv G h_m_obs h_m_kg h_m_jm h_m_units).map x)

/-- Uniqueness up to units quotient. -/
theorem initial_morphism_unique_up_to_units (h_inv : rs_units_invariant_hypothesis) (G : Framework)
    (f : ZeroParam.Morphism (RS h_inv) G)
    (h_m_obs : ∀ x, G.observables G.inh.some = Foundation.reciprocity_skew x)
    (h_m_kg : ∀ x, G.k_gate G.inh.some = G.inh.some)
    (h_m_jm : ∀ x, x ∈ (RS h_inv).j_minimizers ↔ G.inh.some ∈ G.j_minimizers)
    (h_m_units : ∀ u : (RS h_inv).UnitsGroup, G.UnitsAction (G.units_map_const) G.inh.some = G.inh.some)
    (h_unique : initial_morphism_unique_up_to_units_hypothesis h_inv G f h_m_obs h_m_kg h_m_jm h_m_units) :
    ZeroParam.morphismUpToUnits (RS h_inv) G f (initial_morphism h_inv G h_m_obs h_m_kg h_m_jm h_m_units) :=
  h_unique

/-- With Subsingleton target ledger, initial morphism is unique as equality. -/
theorem initial_morphism_unique (h_inv : rs_units_invariant_hypothesis) (G : Framework) [Subsingleton G.ledger]
    (h_m_obs : ∀ x, G.observables G.inh.some = Foundation.reciprocity_skew x)
    (h_m_kg : ∀ x, G.k_gate G.inh.some = G.inh.some)
    (h_m_jm : ∀ x, x ∈ (RS h_inv).j_minimizers ↔ G.inh.some ∈ G.j_minimizers)
    (h_m_units : ∀ u : (RS h_inv).UnitsGroup, G.UnitsAction (G.units_map_const) G.inh.some = G.inh.some)
    (f : ZeroParam.Morphism (RS h_inv) G) : f = initial_morphism h_inv G h_m_obs h_m_kg h_m_jm h_m_units := by
  have : f.map = (initial_morphism h_inv G h_m_obs h_m_kg h_m_jm h_m_units).map := by
    funext x; apply Subsingleton.elim
  exact ZeroParam.morph_eq_of_map_eq this

end RSInitial
end IndisputableMonolith
