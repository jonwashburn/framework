import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace StarOmega8PowMulPow

open IndisputableMonolith.LightLanguage.Basis

/-!
# Star Omega8 Pow Mul Pow Certificate

This certificate proves that `star(ω^n) * ω^m = ω^{7n + m}`.

## Key Result

`∀ n m : ℕ, star (omega8 ^ n) * omega8 ^ m = omega8 ^ (7 * n + m)`

## Why this matters for the certificate chain

This is the **key computational identity** for DFT inner products:

1. **Conjugate as inverse**: star(ω^n) = ω^{-n} = ω^{7n mod 8}
2. **This Lemma**: star(ω^n) * ω^m = ω^{7n + m}
3. **Application**: Sum transformations in orthonormality proofs

This identity is directly used in:
- `sum_star_omega8_pow_prod`: Σ_t star(ω^{tk}) * ω^{tk'} = Σ_t ω^{t(7k+k')}
- DFT column orthonormality proof
- Converting conjugate products to single exponentials

## Mathematical Content

Since:
- star(ω^n) = ω^{-n} = (ω^{-1})^n = (ω^7)^n

We have:
```
star(ω^n) * ω^m = (ω^7)^n * ω^m
               = ω^{7n} * ω^m
               = ω^{7n + m}
```

This converts a conjugate product into a single power of ω.
-/

structure StarOmega8PowMulPowCert where
  deriving Repr

/-- Verification predicate: conjugate power product formula. -/
@[simp] def StarOmega8PowMulPowCert.verified (_c : StarOmega8PowMulPowCert) : Prop :=
  ∀ n m : ℕ, star (omega8 ^ n) * omega8 ^ m = omega8 ^ (7 * n + m)

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem StarOmega8PowMulPowCert.verified_any (c : StarOmega8PowMulPowCert) :
    StarOmega8PowMulPowCert.verified c := by
  intro n m
  exact star_omega8_pow_mul_pow n m

end StarOmega8PowMulPow
end Verification
end IndisputableMonolith
