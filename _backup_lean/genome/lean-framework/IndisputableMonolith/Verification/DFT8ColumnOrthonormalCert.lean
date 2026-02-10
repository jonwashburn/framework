import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace DFT8ColumnOrthonormal

open IndisputableMonolith.LightLanguage.Basis

/-!
# DFT-8 Column Orthonormality Certificate

This certificate packages the proof that DFT-8 columns are orthonormal:

  ⟨column k, column k'⟩ = δ_{k,k'}

## Why this matters for the certificate chain

Column orthonormality is **the** fundamental property of the DFT:

1. **Parseval's theorem**: Energy is preserved under DFT transform.
   ||v||² = ||DFT(v)||² follows from column orthonormality.

2. **Perfect reconstruction**: The inverse DFT exactly recovers the original
   signal because B^H · B = I.

3. **Frequency separation**: Different frequency components are orthogonal,
   so they can be independently analyzed and manipulated.

4. **Unitarity**: Combined with row orthonormality, this proves B is unitary.

## Mathematical Content

For columns k and k':
  ⟨column_k, column_k'⟩ = ∑_t star(B_{t,k}) · B_{t,k'}
                       = ∑_t star(ω^{tk}/√8) · (ω^{tk'}/√8)
                       = (1/8) ∑_t ω^{t(k'-k)}      [using star(ω^n) = ω^{-n}]

For k = k': sum = 8, so inner product = 1
For k ≠ k': sum = 0 (roots of unity sum), so inner product = 0

This is the Kronecker delta: δ_{k,k'} = 1 if k=k', else 0.
-/

structure DFT8ColumnOrthonormalCert where
  deriving Repr

/-- Verification predicate: DFT columns are orthonormal.

This is equivalent to B^H · B = I (unitarity from the column perspective). -/
@[simp] def DFT8ColumnOrthonormalCert.verified (_c : DFT8ColumnOrthonormalCert) : Prop :=
  -- Column orthonormality
  (∀ k k' : Fin 8,
    Finset.univ.sum (fun t : Fin 8 => star (dft8_entry t k) * dft8_entry t k') =
    if k = k' then 1 else 0) ∧
  -- Row orthonormality (dual property)
  (∀ s t : Fin 8,
    Finset.univ.sum (fun k : Fin 8 => star (dft8_entry s k) * dft8_entry t k) =
    if s = t then 1 else 0)

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem DFT8ColumnOrthonormalCert.verified_any (c : DFT8ColumnOrthonormalCert) :
    DFT8ColumnOrthonormalCert.verified c := by
  constructor
  · exact dft8_column_orthonormal
  · exact dft8_row_orthonormal

end DFT8ColumnOrthonormal
end Verification
end IndisputableMonolith
