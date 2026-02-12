import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace StarOmega8PowMulSame

open IndisputableMonolith.LightLanguage.Basis

/-!
# Star Omega8 Power Mul Same Certificate

This certificate proves that `star(ω^{tk}) * ω^{tk} = 1` for all time-frequency pairs.

## Key Result

`∀ t k : Fin 8, star(omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k.val) = 1`

## Why this matters for the certificate chain

This is the **diagonal case** of the DFT inner product computation:

1. **Inner Product**: `⟨col k, col k⟩ = (1/8) ∑_t star(ω^{tk}) * ω^{tk}`
2. **This Lemma**: Each summand equals 1
3. **Result**: Sum = 8, divided by 8 = 1

This proves that DFT columns have **unit norm**.

## Mathematical Content

For any complex number z with |z| = 1:
```
star(z) * z = |z|² = 1
```

Since `omega8` has unit modulus (|ω| = 1), so does any power `ω^n`:
```
star(ω^n) * ω^n = |ω^n|² = |ω|^{2n} = 1^{2n} = 1
```

The proof uses:
1. `star_omega8_pow`: star(ω^n) = ω⁻¹^n
2. `inv_mul_cancel₀`: ω⁻¹ * ω = 1
3. Power distributivity: (ω⁻¹ * ω)^n = 1^n = 1
-/

structure StarOmega8PowMulSameCert where
  deriving Repr

/-- Verification predicate: conjugate times self equals 1 for all power combinations. -/
@[simp] def StarOmega8PowMulSameCert.verified (_c : StarOmega8PowMulSameCert) : Prop :=
  ∀ t k : Fin 8, star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k.val) = 1

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem StarOmega8PowMulSameCert.verified_any (c : StarOmega8PowMulSameCert) :
    StarOmega8PowMulSameCert.verified c := by
  intro t k
  exact star_omega8_pow_mul_same t k

end StarOmega8PowMulSame
end Verification
end IndisputableMonolith
