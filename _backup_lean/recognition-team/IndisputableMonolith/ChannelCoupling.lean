import IndisputableMonolith.OctaveKernel.VoxelField
import IndisputableMonolith.OctaveKernel.Instances.SpatialLattice3D
import IndisputableMonolith.OctaveKernel.Instances.SpatialCouplingWeights
import Mathlib

/-!
# IndisputableMonolith.OctaveKernel.ChannelCoupling

This module implements the "Unitary Coupled Octave" model (Option B of the formalization plan).

Instead of a single scalar entering photon, each voxel manages a vector of 18 channels
(6 faces + 12 edges). The evolution is unitary by construction, ensuring global
energy conservation.
-/

namespace IndisputableMonolith
namespace OctaveKernel

open MeaningfulVoxelField
open Instances

/-! ## B0: Minimal new types -/

/-- Direction index for coupling: 6 faces + 12 edges = 18 channels. -/
def Dir : Type := Sum (Fin 6) (Fin 12)

instance : Fintype Dir := inferInstanceAs (Fintype (Sum (Fin 6) (Fin 12)))

/-- A vector of complex amplitudes, one for each direction. -/
def ChannelVec := Dir → ℂ

/-- Energy (squared norm) of a channel vector. -/
noncomputable def channelEnergy (ψ : ChannelVec) : ℝ :=
  ∑ d, Complex.normSq (ψ d)

/-- Inner product of two channel vectors. -/
noncomputable def channelInner (ψ φ : ChannelVec) : ℂ :=
  ∑ d, (ψ d) * (Complex.conj (φ d))

/-- Energy is exactly the self-inner-product. -/
theorem channelEnergy_eq_inner (ψ : ChannelVec) :
    (channelEnergy ψ : ℂ) = channelInner ψ ψ := by
  unfold channelEnergy channelInner
  simp only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum, mul_comm]

/-- Inner product linearity/conjugate-linearity. -/
theorem channelInner_add_left (ψ1 ψ2 φ : ChannelVec) :
    channelInner (fun d => ψ1 d + ψ2 d) φ = channelInner ψ1 φ + channelInner ψ2 φ := by
  unfold channelInner
  simp only [add_mul, Finset.sum_add_distrib]

theorem channelInner_mul_left (c : ℂ) (ψ φ : ChannelVec) :
    channelInner (fun d => c * ψ d) φ = c * channelInner ψ φ := by
  unfold channelInner
  simp only [mul_assoc, Finset.mul_sum]

theorem channelInner_add_right (ψ φ1 φ2 : ChannelVec) :
    channelInner ψ (fun d => φ1 d + φ2 d) = channelInner ψ φ1 + channelInner ψ φ2 := by
  unfold channelInner
  simp only [Complex.conj_add, mul_add, Finset.sum_add_distrib]

theorem channelInner_mul_right (c : ℂ) (ψ φ : ChannelVec) :
    channelInner ψ (fun d => c * φ d) = (Complex.conj c) * channelInner ψ φ := by
  unfold channelInner
  simp only [Complex.conj_mul, mul_assoc, mul_left_comm, Finset.mul_sum]

theorem channelInner_conj_symm (ψ φ : ChannelVec) :
    channelInner ψ φ = Complex.conj (channelInner φ ψ) := by
  unfold channelInner
  simp only [Complex.conj_sum, Complex.conj_mul, Complex.conj_conj, mul_comm]

/-! ## B2: Local "coin" / scattering unitary -/

section Coin

/-- The normalized "face-average" mode. -/
noncomputable def faceAvgBasis : ChannelVec := fun d =>
  match d with
  | Sum.inl _ => 1 / (Real.sqrt 6 : ℂ)
  | Sum.inr _ => 0

/-- The normalized "edge-average" mode. -/
noncomputable def edgeAvgBasis : ChannelVec := fun d =>
  match d with
  | Sum.inl _ => 0
  | Sum.inr _ => 1 / (Real.sqrt 12 : ℂ)

/-- Basis vectors are normalized and orthogonal. -/
theorem basis_orthonormal :
    (channelInner faceAvgBasis faceAvgBasis = 1) ∧
    (channelInner edgeAvgBasis edgeAvgBasis = 1) ∧
    (channelInner faceAvgBasis edgeAvgBasis = 0) := by
  constructor
  · -- face norm
    unfold channelInner faceAvgBasis
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_zero, Complex.conj_div, Complex.conj_one, Complex.conj_ofReal, Finset.sum_disjSum]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [← mul_inv, ← pow_two]
    have h6 : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
      rw [Complex.ofReal_sqrt (by norm_num), Complex.sq_sqrt]
      norm_num
    simp [h6]
  constructor
  · -- edge norm
    unfold channelInner edgeAvgBasis
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_zero, Complex.conj_div, Complex.conj_one, Complex.conj_ofReal, Finset.sum_disjSum]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [← mul_inv, ← pow_two]
    have h12 : (Real.sqrt 12 : ℂ) ^ 2 = 12 := by
      rw [Complex.ofReal_sqrt (by norm_num), Complex.sq_sqrt]
      norm_num
    simp [h12]
  · -- orthogonality
    unfold channelInner faceAvgBasis edgeAvgBasis
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.conj_zero, Complex.conj_div, Complex.conj_one, Complex.conj_ofReal, Finset.sum_disjSum]
    simp

/-- The 2x2 unitary mixing (coin) operator.
    It rotates the plane spanned by faceAvgBasis and edgeAvgBasis by angle θ. -/
noncomputable def coin (θ : ℝ) (ψ : ChannelVec) : ChannelVec :=
  let c_f := channelInner ψ faceAvgBasis
  let c_e := channelInner ψ edgeAvgBasis
  let d_f := (Complex.ofReal (Real.cos θ)) * c_f - (Complex.ofReal (Real.sin θ)) * c_e
  let d_e := (Complex.ofReal (Real.sin θ)) * c_f + (Complex.ofReal (Real.cos θ)) * c_e
  fun d => ψ d + (d_f - c_f) * (faceAvgBasis d) + (d_e - c_e) * (edgeAvgBasis d)

/-- The local coin preserves energy. -/
theorem coin_preserves_energy (θ : ℝ) (ψ : ChannelVec) :
    channelEnergy (coin θ ψ) = channelEnergy ψ := by
  -- We work in ℂ to use inner products
  rw [← Complex.ofReal_inj]
  simp only [channelEnergy_eq_inner]
  let v_f := faceAvgBasis
  let v_e := edgeAvgBasis
  let c_f := channelInner ψ v_f
  let c_e := channelInner ψ v_e
  let d_f := (Complex.ofReal (Real.cos θ)) * c_f - (Complex.ofReal (Real.sin θ)) * c_e
  let d_e := (Complex.ofReal (Real.sin θ)) * c_f + (Complex.ofReal (Real.cos θ)) * c_e

  -- The coin is an isometry because it's a unitary rotation on a 2D subspace.
  -- Decompose ψ = ψ_perp + c_f * v_f + c_e * v_e where ψ_perp is orthogonal to v_f, v_e.
  let ψ_perp : ChannelVec := fun d => ψ d - c_f * v_f d - c_e * v_e d

  -- 1. Show <ψ_perp, v_f> = 0 and <ψ_perp, v_e> = 0
  have h_perp_f : channelInner ψ_perp v_f = 0 := by
    simp [ψ_perp, channelInner_add_left, channelInner_mul_left, c_f, c_e]
    have h_basis := basis_orthonormal
    simp [h_basis.1, h_basis.2.2]
  have h_perp_e : channelInner ψ_perp v_e = 0 := by
    simp [ψ_perp, channelInner_add_left, channelInner_mul_left, c_f, c_e]
    have h_basis := basis_orthonormal
    simp [h_basis.2.1, h_basis.2.2, channelInner_conj_symm]

  -- 2. Show coin θ ψ = ψ_perp + d_f * v_f + d_e * v_e
  have h_coin_def : coin θ ψ = fun d => ψ_perp d + d_f * v_f d + d_e * v_e d := by
    unfold coin ψ_perp d_f d_e
    ext d
    ring

  -- 3. Show |d_f|^2 + |d_e|^2 = |c_f|^2 + |c_e|^2
  have h_rot : Complex.normSq d_f + Complex.normSq d_e = Complex.normSq c_f + Complex.normSq c_e := by
    simp only [d_f, d_e, Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal]
    ring_nf
    have h_trig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    calc
      (Real.cos θ ^ 2 * Complex.normSq c_f + Real.sin θ ^ 2 * Complex.normSq c_e - 2 * Real.cos θ * Real.sin θ * (c_f * Complex.conj c_e).re) +
      (Real.sin θ ^ 2 * Complex.normSq c_f + Real.cos θ ^ 2 * Complex.normSq c_e + 2 * Real.sin θ * Real.cos θ * (c_f * Complex.conj c_e).re)
      = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * Complex.normSq c_f + (Real.sin θ ^ 2 + Real.cos θ ^ 2) * Complex.normSq c_e := by ring
      _ = 1 * Complex.normSq c_f + 1 * Complex.normSq c_e := by rw [h_trig]
      _ = Complex.normSq c_f + Complex.normSq c_e := by ring

  -- 4. Apply Pythagoras
  rw [h_coin_def]
  simp only [channelInner_add_left, channelInner_add_right, channelInner_mul_left, channelInner_mul_right]
  simp only [h_perp_f, h_perp_e, channelInner_conj_symm v_f ψ_perp, channelInner_conj_symm v_e ψ_perp]
  simp only [Complex.conj_zero, mul_zero, add_zero, zero_add]
  have h_basis := basis_orthonormal
  simp only [h_basis.1, h_basis.2.1, h_basis.2.2, channelInner_conj_symm v_f v_e]
  simp only [Complex.conj_one, Complex.conj_zero, mul_one, mul_zero]

  -- RHS Pythagoras
  have h_ψ_decomp : ψ = fun d => ψ_perp d + c_f * v_f d + c_e * v_e d := by
    simp [ψ_perp]; ext d; ring
  conv_rhs => rw [h_ψ_decomp]
  simp only [channelInner_add_left, channelInner_add_right, channelInner_mul_left, channelInner_mul_right]
  simp only [h_perp_f, h_perp_e, channelInner_conj_symm v_f ψ_perp, channelInner_conj_symm v_e ψ_perp]
  simp only [Complex.conj_zero, mul_zero, add_zero, zero_add]
  simp only [h_basis.1, h_basis.2.1, h_basis.2.2, channelInner_conj_symm v_f v_e]
  simp only [Complex.conj_one, Complex.conj_zero, mul_one, mul_zero]

  -- Final identity
  simp only [← Complex.normSq_eq_conj_mul_self]
  rw [add_assoc, h_rot, add_assoc]

/-- The coin operator is reversible (it's a rotation). -/
noncomputable def coinInv (θ : ℝ) (ψ : ChannelVec) : ChannelVec :=
  coin (-θ) ψ

theorem coin_inv_left (θ : ℝ) (ψ : ChannelVec) :
    coinInv θ (coin θ ψ) = ψ := by
  unfold coinInv coin
  -- Coefficients of coin θ ψ are (d_f, d_e).
  -- Rotating them by -θ should return (c_f, c_e).
  let c_f := channelInner ψ faceAvgBasis
  let c_e := channelInner ψ edgeAvgBasis
  let d_f := (Complex.ofReal (Real.cos θ)) * c_f - (Complex.ofReal (Real.sin θ)) * c_e
  let d_e := (Complex.ofReal (Real.sin θ)) * c_f + (Complex.ofReal (Real.cos θ)) * c_e

  let ψ' := fun d => ψ d + (d_f - c_f) * (faceAvgBasis d) + (d_e - c_e) * (edgeAvgBasis d)

  have h_df' : channelInner ψ' faceAvgBasis = d_f := by
    simp [ψ', channelInner_add_left, channelInner_mul_left, c_f]
    have h_basis := basis_orthonormal
    simp [h_basis.1, h_basis.2.2]
  have h_de' : channelInner ψ' edgeAvgBasis = d_e := by
    simp [ψ', channelInner_add_left, channelInner_mul_left, c_e]
    have h_basis := basis_orthonormal
    simp [h_basis.2.1, h_basis.2.2, channelInner_conj_symm]

  let d_f' := (Complex.ofReal (Real.cos (-θ))) * d_f - (Complex.ofReal (Real.sin (-θ))) * d_e
  let d_e' := (Complex.ofReal (Real.sin (-θ))) * d_f + (Complex.ofReal (Real.cos (-θ))) * d_e

  have h_rot_back : d_f' = c_f ∧ d_e' = c_e := by
    simp [d_f', d_e', d_f, d_e, Real.cos_neg, Real.sin_neg]
    constructor <;> ring_nf
    · have h_trig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
      calc
        c_f * (Real.cos θ ^ 2 + Real.sin θ ^ 2) = c_f * 1 := by rw [h_trig]
        _ = c_f := by ring
    · have h_trig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
      calc
        c_e * (Real.cos θ ^ 2 + Real.sin θ ^ 2) = c_e * 1 := by rw [h_trig]
        _ = c_e := by ring

  simp only [h_df', h_de', h_rot_back.1, h_rot_back.2]
  ext d
  simp [ψ']
  ring

end Coin

/-! ## B1: Routing permutation -/

section Routing

variable {Pos : Type} [Fintype Pos]

/-- Routing: each voxel p's direction d channel comes from its neighbor's exiting channel. -/
def route (L : MeaningfulVoxelField.VoxelLattice Pos) (ψ : Pos → ChannelVec) : Pos → ChannelVec :=
  fun p d =>
    match d with
    | Sum.inl d6 => ψ (L.faceSrc p d6) (Sum.inl d6)
    | Sum.inr d12 => ψ (L.edgeSrc p d12) (Sum.inr d12)

/-- Routing preserves global energy because it's a permutation of amplitudes. -/
theorem route_preserves_energy (L : MeaningfulVoxelField.VoxelLattice Pos)
    (h_perm : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (h_perm_edge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d))
    (ψ : Pos → ChannelVec) :
    ∑ p, channelEnergy (route L ψ p) = ∑ p, channelEnergy (ψ p) := by
  unfold channelEnergy route
  simp only [Finset.sum_disjSum]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s₂ := Finset.univ) (f := fun d p => Complex.normSq (ψ (L.edgeSrc p d) (Sum.inr d)))]
  congr 1
  · ext d; let f := fun p => L.faceSrc p d; have : Function.Bijective f := h_perm d
    rw [Finset.sum_bij f] <;> (intro p _; simp [this.injective, this.surjective q])
  · ext d; let f := fun p => L.edgeSrc p d; have : Function.Bijective f := h_perm_edge d
    rw [Finset.sum_bij f] <;> (intro p _; simp [this.injective, this.surjective q])

/-- Routing is reversible if the lattice mappings are bijections. -/
noncomputable def routeInv (L : MeaningfulVoxelField.VoxelLattice Pos)
    (hFace : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (hEdge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d))
    (ψ : Pos → ChannelVec) : Pos → ChannelVec :=
  fun p d =>
    match d with
    | Sum.inl d6 => ψ (Classical.choose ((hFace d6).surjective p)) (Sum.inl d6)
    | Sum.inr d12 => ψ (Classical.choose ((hEdge d12).surjective p)) (Sum.inr d12)

end Routing

/-! ## B3: Integrate the octave pipeline -/

structure ChannelizedField (Pos : Type) where
  voxel : Pos → Voxel ChannelVec

namespace ChannelizedField

variable {Pos : Type} [Fintype Pos]

noncomputable def totalEnergy (field : ChannelizedField Pos) : ℝ :=
  ∑ p, ∑ phase, channelEnergy ((field.voxel p).slot phase)

noncomputable def stepUnitary (θ : ℝ) (L : VoxelLattice Pos) (field : ChannelizedField Pos) :
    ChannelizedField Pos :=
  let exiting := fun p => (field.voxel p).slot 7
  let routed := route L exiting
  let mixed := fun p => coin θ (routed p)
  ⟨fun p => (field.voxel p).step (mixed p)⟩

/-- Unitary step preserves global field energy. -/
theorem stepUnitary_preserves_energy (θ : ℝ) (L : VoxelLattice Pos)
    (hFace : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (hEdge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d))
    (field : ChannelizedField Pos) :
    (stepUnitary θ L field).totalEnergy = field.totalEnergy := by
  unfold totalEnergy stepUnitary
  simp only [Voxel.step, Fin.sum_univ_eight, ↓reduceIte]
  have h0 : (∑ p, channelEnergy (coin θ (route L (fun p => (field.voxel p).slot 7) p))) =
            (∑ p, channelEnergy ((field.voxel p).slot 7)) := by
    simp only [coin_preserves_energy]
    exact route_preserves_energy L hFace hEdge (fun p => (field.voxel p).slot 7)
  rw [h0]
  have h_split : ∀ p, (∑ k : Phase, channelEnergy ((field.voxel p).slot k)) =
                      (∑ i : Fin 7, channelEnergy ((field.voxel p).slot i.castSucc)) +
                      channelEnergy ((field.voxel p).slot 7) := by
    intro p; exact Fin.sum_univ_eight_last (fun k => channelEnergy ((field.voxel p).slot k))
  simp only [h_split, Finset.sum_add_distrib]
  have h_idx : ∀ p, (∑ i : Fin 7, channelEnergy ((field.voxel p).slot ⟨i.val + 1 - 1, by omega⟩)) =
                    (∑ i : Fin 7, channelEnergy ((field.voxel p).slot i.castSucc)) := by
    intro p; congr; ext i; simp; exact Fin.castSucc_eq i
  simp only [h_idx]; ring

/-! ## Track D: Second-order effects -/

def stepVoxelInv (v : Voxel ChannelVec) (exiting : ChannelVec) : Voxel ChannelVec :=
  ⟨fun p =>
    if h : p = 7 then exiting
    else v.slot ⟨p.val + 1, by
      have : p.val < 7 := by apply Nat.lt_of_le_of_ne; · exact Fin.is_le p; · intro hp; exact h (Fin.ext hp)
      omega⟩⟩

noncomputable def stepUnitaryInv (θ : ℝ) (L : VoxelLattice Pos)
    (hFace : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (hEdge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d))
    (field : ChannelizedField Pos) : ChannelizedField Pos :=
  let unmixed := fun p => coin (-θ) ((field.voxel p).slot 0)
  let unrouted := routeInv L hFace hEdge unmixed
  ⟨fun p => stepVoxelInv (field.voxel p) (unrouted p)⟩

theorem stepUnitary_reversible (θ : ℝ) (L : VoxelLattice Pos)
    (hFace : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (hEdge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d)) :
    Function.Bijective (fun (field : ChannelizedField Pos) => stepUnitary θ L field) := by
  apply Function.bijective_iff_has_inverse.mpr
  use stepUnitaryInv θ L hFace hEdge
  constructor
  · -- left inverse: stepUnitaryInv (stepUnitary field) = field
    intro field; unfold stepUnitary stepUnitaryInv; ext p phase
    simp only [Voxel.step, stepVoxelInv, Voxel.slot, dite_eq_ite]
    split_ifs with h7
    · -- phase = 7
      subst h7
      simp only [routeInv, route, coin_inv_left, Classical.choose_spec]
      ext d; cases d <;> simp only [Classical.choose_spec]
    · -- phase < 7
      rfl
  · -- right inverse: stepUnitary (stepUnitaryInv field) = field
    intro field; unfold stepUnitary stepUnitaryInv; ext p phase
    simp only [Voxel.step, stepVoxelInv, Voxel.slot, dite_eq_ite]
    split_ifs with h0
    · -- phase = 0
      subst h0
      simp only [routeInv, route, coin_inv_left, Classical.choose_spec]
      have h_route : route L (routeInv L hFace hEdge (fun q => coin (-θ) ((field.voxel q).slot 0))) p =
                     coin (-θ) ((field.voxel p).slot 0) := by
        unfold route routeInv
        ext d; cases d <;> simp only [Classical.choose_spec]
      rw [h_route, coin_inv_left]
    · -- phase > 0
      simp only [stepVoxelInv, Voxel.slot]
      have h_ne : (⟨phase.val - 1, by omega⟩ : Fin 8) ≠ 7 := by
        intro he; apply h0; ext; simpa [he] using (Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h)))))
      simp only [h_ne, ↓reduceIte]
      congr; omega

theorem finite_propagation_speed (θ : ℝ) (L : VoxelLattice Pos) (p : Pos) :
    ∀ (f1 f2 : ChannelizedField Pos),
      (f1.voxel p = f2.voxel p) ∧
      (∀ d, f1.voxel (L.faceSrc p d) = f2.voxel (L.faceSrc p d)) ∧
      (∀ d, f1.voxel (L.edgeSrc p d) = field2.voxel (L.edgeSrc p d)) →
      (stepUnitary θ L f1).voxel p = (stepUnitary θ L f2).voxel p := by
  intro f1 f2 ⟨h_p, h_face, h_edge⟩; unfold stepUnitary; simp only [h_p]; congr; unfold route coin
  simp only [h_p, h_face, h_edge]

noncomputable def stepUnitary₀ {Pos : Type} [Fintype Pos] (L : VoxelLattice Pos) :
    ChannelizedField Pos → ChannelizedField Pos := stepUnitary θ₀ L

theorem global_energy_conservation (L : VoxelLattice Pos)
    (hFace : ∀ d, Function.Bijective (fun p => L.faceSrc p d))
    (hEdge : ∀ d, Function.Bijective (fun p => L.edgeSrc p d))
    (field : ChannelizedField Pos) :
    (stepUnitary θ L field).totalEnergy = field.totalEnergy :=
  stepUnitary_preserves_energy θ L hFace hEdge field

end ChannelizedField

noncomputable def projectField {Pos : Type} (field : ChannelizedField Pos) : MeaningfulVoxelField Pos :=
  ⟨fun p => let v := field.voxel p; ⟨fun phase => Photon.ofComplex (∑ d, v.slot phase d)⟩⟩

end OctaveKernel
end IndisputableMonolith
