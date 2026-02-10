import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace DFT8RowOrthonormal

open IndisputableMonolith.LightLanguage.Basis

/-!
# DFT-8 Row Orthonormality Certificate

This certificate proves that the rows of the DFT-8 matrix are orthonormal.

## Key Result

`∀ s t : Fin 8, Σ_k star(B_{s,k}) * B_{t,k} = δ_{s,t}`

## Why this matters for the certificate chain

This is the **row orthonormality** property of the DFT matrix:

1. **Column orthonormality** (certified as #105): `⟨col k, col k'⟩ = δ_{k,k'}`
2. **This Lemma**: `⟨row s, row t⟩ = δ_{s,t}`
3. **Together**: B is unitary (B^H B = B B^H = I)

Row orthonormality means the DFT matrix maps orthonormal vectors to orthonormal
vectors when applied from the right (frequency-domain orthonormality).

## Mathematical Content

The proof exploits the **symmetry** of DFT entries:
```
B_{s,k} = ω^{sk}/√8 = ω^{ks}/√8 = B_{k,s}
```

Therefore:
```
∑_k star(B_{s,k}) * B_{t,k} = ∑_k star(B_{k,s}) * B_{k,t}
                            = ⟨col s, col t⟩
                            = δ_{s,t}  (by column orthonormality)
```

This elegant proof reduces row orthonormality to column orthonormality via symmetry.
-/

structure DFT8RowOrthonormalCert where
  deriving Repr

/-- Verification predicate: rows are orthonormal. -/
@[simp] def DFT8RowOrthonormalCert.verified (_c : DFT8RowOrthonormalCert) : Prop :=
  ∀ s t : Fin 8,
    Finset.univ.sum (fun k : Fin 8 => star (dft8_entry s k) * dft8_entry t k) =
    if s = t then 1 else 0

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem DFT8RowOrthonormalCert.verified_any (c : DFT8RowOrthonormalCert) :
    DFT8RowOrthonormalCert.verified c := by
  intro s t
  exact dft8_row_orthonormal s t

end DFT8RowOrthonormal
end Verification
end IndisputableMonolith
