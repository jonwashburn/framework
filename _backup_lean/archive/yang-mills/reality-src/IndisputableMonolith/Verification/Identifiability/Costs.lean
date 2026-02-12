import Mathlib
import IndisputableMonolith.Verification.Identifiability.Observations

namespace IndisputableMonolith
namespace Verification
namespace Identifiability

/-! Classical gate (choice-dependent): this file uses `UD_explicit` and
    `observe` which depend on classical choice upstream. We fence any
    classical openings locally and avoid leaking `open Classical` globally. -/

noncomputable section

open Classical

noncomputable def l2 (x y : ℝ) : ℝ := (x - y) ^ 2

@[simp] lemma l2_nonneg (x y : ℝ) : 0 ≤ l2 x y := by
  simpa [l2] using sq_nonneg (x - y)

@[simp] lemma l2_eq_zero_iff (x y : ℝ) : l2 x y = 0 ↔ x = y := by
  simpa [l2, sub_eq_zero] using sq_eq_zero_iff (x - y)

lemma add_eq_zero_iff_of_nonneg {a b : ℝ}
  (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha_le : a ≤ 0 := by
      have := le_add_of_nonneg_right hb
      simpa [h] using this
    have hb_le : b ≤ 0 := by
      have := le_add_of_nonneg_left ha
      simpa [h] using this
    exact ⟨le_antisymm ha_le ha, le_antisymm hb_le hb⟩
  · rintro ⟨ha0, hb0⟩
    simp [ha0, hb0]

noncomputable def listPenalty : List ℝ → List ℝ → ℝ
| [], [] => 0
| x :: xs, y :: ys => l2 x y + listPenalty xs ys
| [], _ :: _ => 1
| _ :: _, [] => 1

lemma listPenalty_nonneg : ∀ xs ys : List ℝ, 0 ≤ listPenalty xs ys
| [], [] => by simp [listPenalty]
| x :: xs, y :: ys =>
    have hx : 0 ≤ l2 x y := l2_nonneg x y
    have htail : 0 ≤ listPenalty xs ys := listPenalty_nonneg xs ys
    by
      have := add_nonneg hx htail
      simpa [listPenalty]
| [], _ :: _ => by simp [listPenalty]
| _ :: _, [] => by simp [listPenalty]

lemma listPenalty_eq_zero_iff :
  ∀ xs ys : List ℝ, listPenalty xs ys = 0 ↔ xs = ys
| [], [] => by simp [listPenalty]
| x :: xs, [] => by simp [listPenalty]
| [], y :: ys => by simp [listPenalty]
| x :: xs, y :: ys => by
    have hx : 0 ≤ l2 x y := l2_nonneg x y
    have htail : 0 ≤ listPenalty xs ys := listPenalty_nonneg xs ys
    constructor
    · intro h
      have hsplit :=
        (add_eq_zero_iff_of_nonneg hx htail).mp (by simpa [listPenalty] using h)
      rcases hsplit with ⟨hx0, htail0⟩
      have hx_eq : x = y := (l2_eq_zero_iff x y).mp hx0
      have htail_eq : xs = ys := (listPenalty_eq_zero_iff xs ys).mp htail0
      simpa [hx_eq, htail_eq]
    · intro h
      cases h
      simp [listPenalty, (l2_eq_zero_iff x x).mpr rfl,
        (listPenalty_eq_zero_iff xs xs).mpr rfl]

noncomputable def defaultCost (φ : ℝ) (obs : ObservedLedger φ) : ℝ :=
  let U := UD_explicit φ
  l2 obs.alpha U.alpha0
  + listPenalty obs.massRatios U.massRatios0
  + listPenalty obs.mixingAngles U.mixingAngles0
  + l2 obs.g2Muon U.g2Muon0

lemma defaultCost_nonneg (φ : ℝ) (obs : ObservedLedger φ) : 0 ≤ defaultCost φ obs := by
  have := l2_nonneg obs.alpha (UD_explicit φ).alpha0
  have hb := listPenalty_nonneg obs.massRatios (UD_explicit φ).massRatios0
  have hc := listPenalty_nonneg obs.mixingAngles (UD_explicit φ).mixingAngles0
  have := l2_nonneg obs.g2Muon (UD_explicit φ).g2Muon0
  simp [defaultCost, add_nonneg, *, add_comm, add_left_comm, add_assoc]

lemma defaultCost_eq_zero_iff (φ : ℝ) (obs : ObservedLedger φ) :
  defaultCost φ obs = 0 ↔
    obs.alpha = (UD_explicit φ).alpha0 ∧
    obs.massRatios = (UD_explicit φ).massRatios0 ∧
    obs.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
    obs.g2Muon = (UD_explicit φ).g2Muon0 := by
  have ha := l2_nonneg obs.alpha (UD_explicit φ).alpha0
  have hb := listPenalty_nonneg obs.massRatios (UD_explicit φ).massRatios0
  have hc := listPenalty_nonneg obs.mixingAngles (UD_explicit φ).mixingAngles0
  have hd := l2_nonneg obs.g2Muon (UD_explicit φ).g2Muon0
  constructor
  · intro h
    have := (add_eq_zero_iff_of_nonneg (add_nonneg ha hb) (add_nonneg hc hd)).mp
      (by simpa [defaultCost, add_comm, add_left_comm, add_assoc] using h)
    rcases this with ⟨hsum1, hsum2⟩
    have hαβ := (add_eq_zero_iff_of_nonneg ha hb).mp hsum1
    have hγδ := (add_eq_zero_iff_of_nonneg hc hd).mp hsum2
    rcases hαβ with ⟨hα0, hβ0⟩
    rcases hγδ with ⟨hγ0, hδ0⟩
    have hα := (l2_eq_zero_iff obs.alpha (UD_explicit φ).alpha0).mp hα0
    have hβ := (listPenalty_eq_zero_iff obs.massRatios (UD_explicit φ).massRatios0).mp hβ0
    have hγ := (listPenalty_eq_zero_iff obs.mixingAngles (UD_explicit φ).mixingAngles0).mp hγ0
    have hδ := (l2_eq_zero_iff obs.g2Muon (UD_explicit φ).g2Muon0).mp hδ0
    exact ⟨hα, hβ, hγ, hδ⟩
  · rintro ⟨hα, hβ, hγ, hδ⟩
    simp [defaultCost, hα, hβ, hγ, hδ, listPenalty_eq_zero_iff]

noncomputable def costOf (φ : ℝ) (F : ZeroParamFramework φ) : ℝ :=
  defaultCost φ (observe φ F)

lemma costOf_nonneg (φ : ℝ) (F : ZeroParamFramework φ) :
    0 ≤ costOf φ F :=
  defaultCost_nonneg φ (observe φ F)

lemma costOf_eq_zero (φ : ℝ) (F : ZeroParamFramework φ) : costOf φ F = 0 := by
  have hobs : observe φ F = observedFromUD φ (UD_explicit φ) := observe_eq_ud φ F
  have htarget :
      (observedFromUD φ (UD_explicit φ)).alpha = (UD_explicit φ).alpha0 ∧
      (observedFromUD φ (UD_explicit φ)).massRatios = (UD_explicit φ).massRatios0 ∧
      (observedFromUD φ (UD_explicit φ)).mixingAngles = (UD_explicit φ).mixingAngles0 ∧
      (observedFromUD φ (UD_explicit φ)).g2Muon = (UD_explicit φ).g2Muon0 := by
    simp [observedFromUD]
  have hzero : defaultCost φ (observedFromUD φ (UD_explicit φ)) = 0 :=
    (defaultCost_eq_zero_iff φ (observedFromUD φ (UD_explicit φ))).mpr htarget
  simpa [costOf, hobs]

lemma costOf_eq_zero_of_observe_eq_ud (φ : ℝ) (F : ZeroParamFramework φ)
    (hobs : observe φ F = observedFromUD φ (UD_explicit φ)) :
    costOf φ F = 0 := by
  unfold costOf
  have htarget :
      (observedFromUD φ (UD_explicit φ)).alpha = (UD_explicit φ).alpha0 ∧
      (observedFromUD φ (UD_explicit φ)).massRatios = (UD_explicit φ).massRatios0 ∧
      (observedFromUD φ (UD_explicit φ)).mixingAngles = (UD_explicit φ).mixingAngles0 ∧
      (observedFromUD φ (UD_explicit φ)).g2Muon = (UD_explicit φ).g2Muon0 := by
    simp [observedFromUD]
  simpa [hobs]
    using (defaultCost_eq_zero_iff φ (observedFromUD φ (UD_explicit φ))).mpr htarget

lemma observe_eq_ud_of_cost_zero (φ : ℝ) (F : ZeroParamFramework φ)
    (h : costOf φ F = 0) :
    observe φ F = observedFromUD φ (UD_explicit φ) := by
  -- Deterministic observation is definitionally the explicit universal target
  rfl

lemma obs_equal_implies_cost_eq (φ : ℝ) {F G : ZeroParamFramework φ}
  (hObs : ObsEqual φ F G) : costOf φ F = costOf φ G := by
  unfold costOf
  simpa [hObs]

end Identifiability
end Verification
end IndisputableMonolith

end  -- noncomputable classical fence
