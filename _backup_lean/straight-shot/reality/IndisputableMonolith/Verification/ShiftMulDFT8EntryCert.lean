import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace ShiftMulDFT8Entry

open IndisputableMonolith.LightLanguage.Basis

/-!
# Shift Matrix Acting on DFT Entry Certificate

This certificate proves that the shift operator scales each DFT column by its eigenvalue.

## Key Result

`(S * B)_{t,j} = ω^j * B_{t,j}`

where S is the cyclic shift matrix and B is the DFT-8 matrix.

## Why this matters for the certificate chain

This lemma is the **matrix-form** of the eigenvector property:

1. **Eigenvector Property**: `S(dft8_mode j) = ω^j · (dft8_mode j)`
2. **Matrix Entry Form**: `(S * B)_{t,j} = ω^j * B_{t,j}` ← THIS CERTIFICATE

## Mathematical Content

The cyclic shift matrix S has entries:
  `S_{t,s} = 1  if s = (t+1) mod 8, else 0`

The DFT matrix B has entries:
  `B_{t,k} = ω^{tk} / √8`

Matrix multiplication gives:
```
(S * B)_{t,j} = ∑_s S_{t,s} * B_{s,j}
             = B_{(t+1) mod 8, j}      (only s = (t+1) mod 8 contributes)
             = ω^{((t+1) mod 8) * j} / √8
             = ω^{(t+1)*j} / √8        (since ω^8 = 1)
             = ω^{tj + j} / √8
             = ω^j * ω^{tj} / √8
             = ω^j * B_{t,j}
```

This shows that DFT columns are eigenvectors of the shift operator.
-/

structure ShiftMulDFT8EntryCert where
  deriving Repr

/-- Verification predicate: shift matrix times DFT entry equals eigenvalue times entry. -/
@[simp] def ShiftMulDFT8EntryCert.verified (_c : ShiftMulDFT8EntryCert) : Prop :=
  ∀ t j : Fin 8,
    (shift_matrix * dft8_matrix) t j = (omega8 ^ j.val) * dft8_matrix t j

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem ShiftMulDFT8EntryCert.verified_any (c : ShiftMulDFT8EntryCert) :
    ShiftMulDFT8EntryCert.verified c := by
  intro t j
  exact shift_mul_dft8_entry t j

end ShiftMulDFT8Entry
end Verification
end IndisputableMonolith
