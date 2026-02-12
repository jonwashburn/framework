import Mathlib

/-!
Scalar functional calculus and gap positivity (self-contained lemmas).

Definitions:
  • Tγ := (exp (−γ)) • Id
  • Hγ := γ • Id

Results:
  • isSelfAdjoint_TsmulId, quadPos_TsmulId
  • isSelfAdjoint_HsmulId, quadPos_HsmulId
  • neg_log_exp_neg_eq
-/

namespace YM.SpectralStability.ScalarFC

open Complex

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

noncomputable section

/-- Scalar transfer operator Tγ := exp(−γ) • Id. -/
def Tgamma (γ : ℝ) : X →L[ℂ] X :=
  (Complex.ofReal (Real.exp (−γ))) • ContinuousLinearMap.id ℂ X

/-- Scalar generator Hγ := γ • Id. -/
def Hgamma (γ : ℝ) : X →L[ℂ] X :=
  (Complex.ofReal γ) • ContinuousLinearMap.id ℂ X

theorem isSelfAdjoint_TsmulId {γ : ℝ} : IsSelfAdjoint (Tgamma (X:=X) γ) := by
  -- Id is self-adjoint and the scalar is real
  have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ X) :=
    ContinuousLinearMap.isSelfAdjoint_id
  have hconj : Complex.conj (Complex.ofReal (Real.exp (−γ)))
      = Complex.ofReal (Real.exp (−γ)) := by simp
  simpa [Tgamma, ContinuousLinearMap.smul_def, hconj]
    using hId.smul (Complex.ofReal (Real.exp (−γ)))

theorem quadPos_TsmulId {γ : ℝ} (ψ : X) :
    0 ≤ Complex.realPart ⟪ψ, (Tgamma (X:=X) γ) ψ⟫_ℂ := by
  -- Real part equals exp(−γ) · ‖ψ‖^2 ≥ 0
  have hpos : 0 ≤ Real.exp (−γ) := (Real.exp_pos (−γ)).le
  -- Use linearity in the second argument: ⟪ψ, a • ψ⟫ = a * ⟪ψ, ψ⟫
  have hlin : ⟪ψ, (Tgamma (X:=X) γ) ψ⟫_ℂ
      = (Complex.ofReal (Real.exp (−γ))) * ⟪ψ, ψ⟫_ℂ := by
    dsimp [Tgamma]
    simpa using inner_smul_right (x:=ψ) (a:=Complex.ofReal (Real.exp (−γ))) (y:=ψ)
  -- realPart ((ofReal r) * z) = r * realPart z
  have hreal : Complex.realPart
      ((Complex.ofReal (Real.exp (−γ))) * ⟪ψ, ψ⟫_ℂ)
      = (Real.exp (−γ)) * Complex.realPart ⟪ψ, ψ⟫_ℂ := by
    -- general formula specializes since the scalar is real
    simpa using Complex.realPart_mul (Complex.ofReal (Real.exp (−γ))) ⟪ψ, ψ⟫_ℂ
  -- Conclude using realInner = ‖·‖^2
  have : Complex.realPart ⟪ψ, (Tgamma (X:=X) γ) ψ⟫_ℂ
        = (Real.exp (−γ)) * ‖ψ‖ ^ 2 := by
    simpa [hlin, hreal, Complex.real_inner_self_eq_norm_sq]
  have hnnsq : 0 ≤ ‖ψ‖ ^ 2 := by exact sq_nonneg ‖ψ‖
  exact by
    have := mul_nonneg hpos hnnsq
    simpa [this]

theorem isSelfAdjoint_HsmulId {γ : ℝ} : IsSelfAdjoint (Hgamma (X:=X) γ) := by
  have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ X) :=
    ContinuousLinearMap.isSelfAdjoint_id
  have hconj : Complex.conj (Complex.ofReal γ) = Complex.ofReal γ := by simp
  simpa [Hgamma, ContinuousLinearMap.smul_def, hconj]
    using hId.smul (Complex.ofReal γ)

theorem quadPos_HsmulId {γ : ℝ} (hγ : 0 < γ) (ψ : X) :
    0 ≤ Complex.realPart ⟪ψ, (Hgamma (X:=X) γ) ψ⟫_ℂ := by
  -- Real part equals γ · ‖ψ‖^2 ≥ 0
  have hnn : 0 ≤ γ := le_of_lt hγ
  have hlin : ⟪ψ, (Hgamma (X:=X) γ) ψ⟫_ℂ
      = (Complex.ofReal γ) * ⟪ψ, ψ⟫_ℂ := by
    dsimp [Hgamma]
    simpa using inner_smul_right (x:=ψ) (a:=Complex.ofReal γ) (y:=ψ)
  have hreal : Complex.realPart ((Complex.ofReal γ) * ⟪ψ, ψ⟫_ℂ)
      = γ * Complex.realPart ⟪ψ, ψ⟫_ℂ := by
    simpa using Complex.realPart_mul (Complex.ofReal γ) ⟪ψ, ψ⟫_ℂ
  have : Complex.realPart ⟪ψ, (Hgamma (X:=X) γ) ψ⟫_ℂ = γ * ‖ψ‖ ^ 2 := by
    simpa [hlin, hreal, Complex.real_inner_self_eq_norm_sq]
  have hnnsq : 0 ≤ ‖ψ‖ ^ 2 := by exact sq_nonneg ‖ψ‖
  exact by
    have := mul_nonneg hnn hnnsq
    simpa [this]

theorem neg_log_exp_neg_eq {γ : ℝ} (hγ : 0 < γ) :
    -Real.log (Real.exp (−γ)) = γ := by
  simpa using (by have := Real.log_exp (−γ); simpa using congrArg Neg.neg this)

end

end YM.SpectralStability.ScalarFC
