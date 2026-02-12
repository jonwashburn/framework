import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace StarDFT8EntryMul

open IndisputableMonolith.LightLanguage.Basis

/-!
# DFT Entry Conjugate Product Certificate

This certificate proves the identity that factors out the normalization constant
from DFT entry products.

## Key Result

`star(dft8_entry t k) * dft8_entry t k' = star(ω^{tk}) * ω^{tk'} / 8`

## Why this matters for the certificate chain

This lemma connects DFT matrix entries to omega8 powers:

1. **DFT Entry Definition**: `dft8_entry t k = ω^{tk} / √8`
2. **Conjugate Product**: `star(ω^{tk}/√8) * (ω^{tk'}/√8) = star(ω^{tk}) * ω^{tk'} / 8`
3. **Key Algebra**: `star(√8) = √8` (real), so `√8 * √8 = 8`

## Mathematical Content

Given `dft8_entry t k = ω^{tk} / √8`:

```
star(dft8_entry t k) * dft8_entry t k'
= star(ω^{tk} / √8) * (ω^{tk'} / √8)
= (star(ω^{tk}) / star(√8)) * (ω^{tk'} / √8)
= star(ω^{tk}) / √8 * ω^{tk'} / √8      (since √8 is real, star(√8) = √8)
= star(ω^{tk}) * ω^{tk'} / (√8 * √8)
= star(ω^{tk}) * ω^{tk'} / 8
```

This allows inner products to be computed entirely in terms of ω powers.
-/

structure StarDFT8EntryMulCert where
  deriving Repr

/-- Verification predicate: DFT entry conjugate product factors normalization. -/
@[simp] def StarDFT8EntryMulCert.verified (_c : StarDFT8EntryMulCert) : Prop :=
  ∀ t k k' : Fin 8,
    star (dft8_entry t k) * dft8_entry t k' =
    star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k'.val) / 8

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem StarDFT8EntryMulCert.verified_any (c : StarDFT8EntryMulCert) :
    StarDFT8EntryMulCert.verified c := by
  intro t k k'
  exact star_dft8_entry_mul t k k'

end StarDFT8EntryMul
end Verification
end IndisputableMonolith
