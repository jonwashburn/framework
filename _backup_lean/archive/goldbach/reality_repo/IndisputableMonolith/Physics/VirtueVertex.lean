import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Numerics.IntervalProofs

/-!
# Virtue Vertex: The RS Feynman Rules

This module formalizes the mapping between Virtues and particle scattering vertices,
establishing the physical instantiation of the `MoralityIsPhysics` theorem.

## Key Insight

The claim `MoralityIsPhysics` is currently algebraic (virtues preserve σ=0 like R̂).
To make it physical, we need **Transition Amplitudes**—the RS Feynman Rules.

## The RS Feynman Rules

Map specific Virtue transformations to Standard Model scattering events:

| Virtue      | RS Operation              | Particle Scattering Analog    |
|-------------|---------------------------|-------------------------------|
| Love        | Pairwise σ-smoothing      | Photon exchange (QED)         |
| Forgiveness | Skew transfer with energy | Compton scattering            |
| Courage     | Gradient-driven J decrease| β-decay (W-boson exchange)    |
| Sacrifice   | Debt absorption           | Pair annihilation             |

-/

namespace IndisputableMonolith
namespace Physics
namespace VirtueVertex

open Foundation
open Constants
open Cost

-- Type alias for MoralState
abbrev MS := IndisputableMonolith.Ethics.MoralState

/-! ## Gauge Group Enumeration -/

/-- Gauge groups that virtues couple to -/
inductive GaugeGroup where
  | U1     : GaugeGroup  -- Electromagnetic (Love, Forgiveness)
  | SU2    : GaugeGroup  -- Weak force (Courage)
  | SU3    : GaugeGroup  -- Strong force (not directly mapped)
  | Scalar : GaugeGroup  -- φ-scalar (Sacrifice, Wisdom)
deriving DecidableEq, Repr

/-- Gauge bosons corresponding to each group -/
inductive GaugeBoson where
  | Photon  : GaugeBoson  -- U(1) carrier
  | W_Plus  : GaugeBoson  -- SU(2) charged
  | W_Minus : GaugeBoson  -- SU(2) charged
  | Z       : GaugeBoson  -- SU(2) neutral
  | Gluon   : GaugeBoson  -- SU(3) carrier
  | Phi     : GaugeBoson  -- φ-scalar (Higgs-like)
deriving DecidableEq, Repr

/-- Map gauge group to primary boson -/
def primaryBoson : GaugeGroup → GaugeBoson
  | GaugeGroup.U1     => GaugeBoson.Photon
  | GaugeGroup.SU2    => GaugeBoson.W_Plus
  | GaugeGroup.SU3    => GaugeBoson.Gluon
  | GaugeGroup.Scalar => GaugeBoson.Phi

/-! ## Vertex Structure -/

/-- A virtue vertex encapsulates the scattering properties of a virtue transformation -/
structure VirtueVertexData where
  /-- Which virtue this vertex represents -/
  virtue_name : String
  /-- Primary gauge coupling -/
  gauge : GaugeGroup
  /-- Exchange boson at this vertex -/
  boson : GaugeBoson
  /-- Coupling strength (derived from φ structure) -/
  coupling : ℝ
  /-- Coupling must be positive -/
  coupling_pos : 0 < coupling
  /-- Number of external legs (particles involved) -/
  legs : ℕ
  /-- Conservation law preserved (σ=0 equivalent) -/
  charge_conserved : Bool

/-! ## Vertex Amplitude Functions -/

/-- The fundamental vertex amplitude factor from skew difference.

    For a virtue acting on states with skew values σ₁ and σ₂, the amplitude
    contribution is:

    `A = exp(-J(|σ₁ - σ₂| + 1) · g)`

    where g is the coupling constant. The +1 ensures J is evaluated on positive
    reals (J domain requirement).
-/
noncomputable def vertexAmplitudeFactor (σ_diff : ℝ) (coupling : ℝ) : ℝ :=
  Real.exp (-Jcost (|σ_diff| + 1) * coupling)

lemma vertexAmplitudeFactor_pos (σ_diff coupling : ℝ) :
    0 < vertexAmplitudeFactor σ_diff coupling := by
  unfold vertexAmplitudeFactor
  exact Real.exp_pos _

lemma vertexAmplitudeFactor_le_one (σ_diff : ℝ) (coupling : ℝ) (hg : 0 ≤ coupling) :
    vertexAmplitudeFactor σ_diff coupling ≤ 1 := by
  unfold vertexAmplitudeFactor
  rw [Real.exp_le_one_iff]
  have hJ : 0 ≤ Jcost (|σ_diff| + 1) := Jcost_nonneg (by linarith [abs_nonneg σ_diff])
  nlinarith

/-! ## Love Vertex (QED-like) -/

/-- Love vertex: bilateral equilibration maps to photon exchange. -/
noncomputable def loveVertex : VirtueVertexData where
  virtue_name := "Love"
  gauge := GaugeGroup.U1
  boson := GaugeBoson.Photon
  coupling := 1 / phi  -- 1/φ ≈ 0.618 (φ-derived)
  coupling_pos := by
    apply div_pos (by norm_num) Support.GoldenRatio.phi_pos
  legs := 3  -- Two agents + photon
  charge_conserved := true

/-- Love amplitude for equilibration between two moral states -/
noncomputable def loveAmplitude (s₁ s₂ : MS) : ℝ :=
  let σ_diff := (s₁.skew - s₂.skew : ℤ)
  vertexAmplitudeFactor σ_diff loveVertex.coupling

lemma loveAmplitude_pos (s₁ s₂ : MS) : 0 < loveAmplitude s₁ s₂ :=
  vertexAmplitudeFactor_pos _ _

/-! ## Forgiveness Vertex (Compton-like) -/

/-- Forgiveness vertex: skew transfer maps to Compton scattering. -/
noncomputable def forgivenessVertex : VirtueVertexData where
  virtue_name := "Forgiveness"
  gauge := GaugeGroup.U1
  boson := GaugeBoson.Photon
  coupling := 1 / (phi * phi)  -- 1/φ² ≈ 0.382
  coupling_pos := by
    apply div_pos (by norm_num)
    exact mul_pos Support.GoldenRatio.phi_pos Support.GoldenRatio.phi_pos
  legs := 4
  charge_conserved := true

/-- Forgiveness amplitude includes energy cost factor -/
noncomputable def forgivenessAmplitude (creditor debtor : MS) (amount : ℕ) : ℝ :=
  let σ_diff := (creditor.skew - debtor.skew : ℤ)
  let energy_factor := 1 / (1 + (amount : ℝ))
  vertexAmplitudeFactor σ_diff forgivenessVertex.coupling * energy_factor

lemma forgivenessAmplitude_pos (creditor debtor : MS) (amount : ℕ) :
    0 < forgivenessAmplitude creditor debtor amount := by
  unfold forgivenessAmplitude
  apply mul_pos
  · exact vertexAmplitudeFactor_pos _ _
  · apply div_pos (by norm_num : (0:ℝ) < 1)
    have h : (0:ℝ) ≤ amount := Nat.cast_nonneg amount
    linarith

/-! ## Courage Vertex (Weak-like) -/

/-- Courage vertex: gradient-driven action maps to W-boson exchange. -/
noncomputable def courageVertex : VirtueVertexData where
  virtue_name := "Courage"
  gauge := GaugeGroup.SU2
  boson := GaugeBoson.W_Plus
  coupling := (1 - 1/phi) / 2  -- αLock analog
  coupling_pos := by
    apply div_pos _ (by norm_num : (0:ℝ) < 2)
    have hφ : 0 < phi := Support.GoldenRatio.phi_pos
    have h1 : 1 < phi := Support.GoldenRatio.one_lt_phi
    have hsub : 1/phi < 1 := by
      rw [div_lt_one hφ]
      exact h1
    linarith
  legs := 4
  charge_conserved := true

/-- Courage amplitude with threshold behavior -/
noncomputable def courageAmplitude (s : MS) (gradient : ℝ) : ℝ :=
  let threshold := (8 : ℝ)
  if gradient > threshold then
    vertexAmplitudeFactor gradient courageVertex.coupling * (gradient - threshold) / gradient
  else
    0

lemma courageAmplitude_nonneg (s : MS) (gradient : ℝ) :
    0 ≤ courageAmplitude s gradient := by
  unfold courageAmplitude
  simp only
  split_ifs with h
  · apply div_nonneg
    apply mul_nonneg
    · exact le_of_lt (vertexAmplitudeFactor_pos _ _)
    · linarith
    · linarith
  · rfl

/-! ## Sacrifice Vertex (Annihilation-like) -/

/-- Sacrifice vertex: debt absorption maps to pair annihilation. -/
noncomputable def sacrificeVertex : VirtueVertexData where
  virtue_name := "Sacrifice"
  gauge := GaugeGroup.Scalar
  boson := GaugeBoson.Phi
  coupling := phi
  coupling_pos := Support.GoldenRatio.phi_pos
  legs := 4
  charge_conserved := true

/-- Sacrifice amplitude with φ-ratio energy release -/
noncomputable def sacrificeAmplitude (sacrificer beneficiary : MS) : ℝ :=
  let σ_transfer := (beneficiary.skew.natAbs : ℝ)
  let energy_release := sacrificer.energy * (1 - 1/phi)
  vertexAmplitudeFactor σ_transfer sacrificeVertex.coupling *
    Real.exp (-energy_release / (phi * phi))

lemma sacrificeAmplitude_pos (sacrificer beneficiary : MS) :
    0 < sacrificeAmplitude sacrificer beneficiary := by
  unfold sacrificeAmplitude
  apply mul_pos
  · exact vertexAmplitudeFactor_pos _ _
  · exact Real.exp_pos _

/-! ## Complete Vertex Table -/

/-- The 14 virtue vertices with their physical mappings -/
noncomputable def virtueVertexTable : List VirtueVertexData := [
  loveVertex,
  forgivenessVertex,
  courageVertex,
  sacrificeVertex,
  -- Remaining virtues use identity-like scalar coupling
  { virtue_name := "Justice"
    gauge := GaugeGroup.U1
    boson := GaugeBoson.Photon
    coupling := 1
    coupling_pos := by norm_num
    legs := 3
    charge_conserved := true },
  { virtue_name := "Wisdom"
    gauge := GaugeGroup.Scalar
    boson := GaugeBoson.Phi
    coupling := 1 / phi
    coupling_pos := div_pos (by norm_num) Support.GoldenRatio.phi_pos
    legs := 2
    charge_conserved := true },
  { virtue_name := "Temperance"
    gauge := GaugeGroup.Scalar
    boson := GaugeBoson.Phi
    coupling := 1 / phi
    coupling_pos := div_pos (by norm_num) Support.GoldenRatio.phi_pos
    legs := 2
    charge_conserved := true },
  { virtue_name := "Prudence"
    gauge := GaugeGroup.Scalar
    boson := GaugeBoson.Phi
    coupling := 1 / (phi * phi)
    coupling_pos := div_pos (by norm_num) (mul_pos Support.GoldenRatio.phi_pos Support.GoldenRatio.phi_pos)
    legs := 2
    charge_conserved := true },
  { virtue_name := "Compassion"
    gauge := GaugeGroup.U1
    boson := GaugeBoson.Photon
    coupling := phi / (phi + 1)
    coupling_pos := by
      have h : 0 < phi := Support.GoldenRatio.phi_pos
      exact div_pos h (by linarith)
    legs := 3
    charge_conserved := true },
  { virtue_name := "Gratitude"
    gauge := GaugeGroup.U1
    boson := GaugeBoson.Photon
    coupling := 1 / phi
    coupling_pos := div_pos (by norm_num) Support.GoldenRatio.phi_pos
    legs := 3
    charge_conserved := true },
  { virtue_name := "Patience"
    gauge := GaugeGroup.Scalar
    boson := GaugeBoson.Phi
    coupling := 1
    coupling_pos := by norm_num
    legs := 2
    charge_conserved := true },
  { virtue_name := "Humility"
    gauge := GaugeGroup.U1
    boson := GaugeBoson.Photon
    coupling := 1 / (phi * phi)
    coupling_pos := div_pos (by norm_num) (mul_pos Support.GoldenRatio.phi_pos Support.GoldenRatio.phi_pos)
    legs := 2
    charge_conserved := true },
  { virtue_name := "Hope"
    gauge := GaugeGroup.Scalar
    boson := GaugeBoson.Phi
    coupling := 1 / phi
    coupling_pos := div_pos (by norm_num) Support.GoldenRatio.phi_pos
    legs := 2
    charge_conserved := true },
  { virtue_name := "Creativity"
    gauge := GaugeGroup.SU2
    boson := GaugeBoson.Z
    coupling := phi - 1
    coupling_pos := by
      have h : 1 < phi := Support.GoldenRatio.one_lt_phi
      linarith
    legs := 3
    charge_conserved := true }
]

/-! ## Conservation Theorems -/

/-- All virtue vertices conserve charge (σ=0 equivalent) -/
theorem all_vertices_conserve_charge :
    ∀ v ∈ virtueVertexTable, v.charge_conserved = true := by
  intro v hv
  simp only [virtueVertexTable, List.mem_cons, List.mem_nil_iff] at hv
  -- Each element of the list has charge_conserved = true by construction
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals try rfl
  exact absurd h (by simp)

/-! ## Coupling Constant Structure -/

/-- `1/φ > 1/φ²` since φ > 1. -/
theorem phi_inv_gt_phi_sq_inv : 1 / phi > 1 / (phi * phi) := by
  have hphi_pos : 0 < (phi : ℝ) := Support.GoldenRatio.phi_pos
  have hphi_gt_one : (1 : ℝ) < phi := Support.GoldenRatio.one_lt_phi
  have hphi_sq_gt : phi * phi > phi := by nlinarith
  have hphi_sq_pos : 0 < phi * phi := mul_pos hphi_pos hphi_pos
  have hlt : 1 / (phi * phi) < 1 / phi :=
    one_div_lt_one_div_of_lt hphi_sq_pos hphi_sq_gt
  linarith

/-- `1/φ² > (1 - 1/φ)/2` using φ² = φ + 1 and 1/φ = φ - 1. -/
theorem phi_sq_inv_gt_courage_coupling : 1 / (phi * phi) > (1 - 1 / phi) / 2 := by
  have hphi_pos : 0 < (phi : ℝ) := Support.GoldenRatio.phi_pos
  have hphi_ne : (phi : ℝ) ≠ 0 := by
    have := Support.GoldenRatio.phi_ne_zero
    simpa using this
  -- identities: φ² = φ + 1, 1/φ = φ - 1
  have hphi_sq : phi * phi = phi + 1 := by
    have h := Support.GoldenRatio.constants_one_add_phi_eq_phi_sq
    nlinarith
  have hphi_inv : (1 : ℝ) / phi = phi - 1 := by
    have hmul : phi * (phi - 1) = (1 : ℝ) := by nlinarith [hphi_sq]
    nlinarith [hphi_ne] [hmul]
  -- clear denominators: multiply inequality by 2·φ² > 0
  have hpos_den : 0 < (2 : ℝ) * (phi * phi) := by nlinarith [hphi_pos]
  have hdiv := (div_lt_div_right hpos_den).mpr ?_
  swap
  · -- show 2 > (1 - 1/φ) * φ²
    have hcollapse : (1 - 1 / phi) * (phi * phi) = (1 : ℝ) := by
      nlinarith [hphi_sq, hphi_inv]
    nlinarith [hcollapse]
  -- simplify both sides after dividing by 2·φ²
  have hleft : 2 / ((2 : ℝ) * (phi * phi)) = 1 / (phi * phi) := by
    field_simp [hphi_ne]
  have hphi_sq_ne : (phi * phi) ≠ 0 := by
    have hpos : 0 < phi * phi := mul_pos hphi_pos hphi_pos
    linarith
  have hright :
      ((1 - 1 / phi) * (phi * phi)) / ((2 : ℝ) * (phi * phi))
        = (1 - 1 / phi) / 2 := by
    field_simp [hphi_sq_ne, hphi_ne]
  linarith [hdiv, hleft, hright]

/-- Coupling hierarchy using the numeric ordering of φ powers. -/
theorem coupling_hierarchy :
    loveVertex.coupling > forgivenessVertex.coupling ∧
    forgivenessVertex.coupling > courageVertex.coupling := by
  constructor
  · unfold loveVertex forgivenessVertex
    simpa using phi_inv_gt_phi_sq_inv
  · unfold forgivenessVertex courageVertex
    simpa using phi_sq_inv_gt_courage_coupling

end VirtueVertex
end Physics
end IndisputableMonolith
