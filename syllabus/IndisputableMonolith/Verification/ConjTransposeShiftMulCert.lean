import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace ConjTransposeShiftMul

open IndisputableMonolith.LightLanguage.Basis

/-!
# Conjugate Transpose Shift Multiplication Certificate

This certificate proves that `B^H · (S · B)` at entry (i, j) equals `ω^j · δ_{i,j}`.

## Key Result

`(B^H * (S * B))_{i,j} = ω^j * [i = j]`

where B is the DFT-8 matrix, S is the shift matrix, and [·] is the Iverson bracket.

## Why this matters for the certificate chain

This lemma is the **key step** in proving DFT diagonalizes the shift:

1. **This lemma**: `(B^H * (S * B))_{i,j} = ω^j * δ_{i,j}`
2. **Consequence**: `B^H * S * B = diag(1, ω, ω², ..., ω⁷)`

## Mathematical Content

```
(B^H * (S * B))_{i,j}
  = ∑_t star(B_{t,i}) * (S * B)_{t,j}              [matrix multiplication]
  = ∑_t star(B_{t,i}) * (ω^j * B_{t,j})            [by shift_mul_dft8_entry]
  = ω^j * ∑_t star(B_{t,i}) * B_{t,j}              [factor out ω^j]
  = ω^j * δ_{i,j}                                   [by column orthonormality]
```

This proves that the similarity transform `B^H · S · B` yields a diagonal matrix
with eigenvalues (1, ω, ω², ..., ω⁷).
-/

structure ConjTransposeShiftMulCert where
  deriving Repr

/-- Verification predicate: conjugate transpose times shift times DFT matrix
    at entry (i,j) equals ω^j times the Kronecker delta. -/
@[simp] def ConjTransposeShiftMulCert.verified (_c : ConjTransposeShiftMulCert) : Prop :=
  ∀ i j : Fin 8,
    (dft8_matrix.conjTranspose * (shift_matrix * dft8_matrix)) i j =
    (omega8 ^ j.val) * (if i = j then 1 else 0)

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem ConjTransposeShiftMulCert.verified_any (c : ConjTransposeShiftMulCert) :
    ConjTransposeShiftMulCert.verified c := by
  intro i j
  exact conjTranspose_shift_mul i j

end ConjTransposeShiftMul
end Verification
end IndisputableMonolith
