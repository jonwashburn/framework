import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace SumStarOmega8Prod

open IndisputableMonolith.LightLanguage.Basis

/-!
# Sum of Conjugate Products Certificate

This certificate proves the key identity that converts sums of conjugate products
into sums of powers, which is the crucial step for DFT orthonormality.

## Key Result

`∑_t star(ω^{tk}) * ω^{tk'} = ∑_t ω^{t(7k+k')}`

## Why this matters for the certificate chain

This identity is the **bridge** from inner products to roots of unity sums:

1. **DFT Inner Product**: `⟨column k, column k'⟩ = ∑_t star(ω^{tk}/√8) * (ω^{tk'}/√8)`
2. **This Lemma**: Converts to `(1/8) ∑_t ω^{t(7k+k')}`
3. **Roots of Unity**: When k ≠ k', sum = 0; when k = k', sum = 8

## Mathematical Content

Using the power product identity `star(ω^n) * ω^m = ω^{7n+m}`:

```
∑_t star(ω^{tk}) * ω^{tk'}
= ∑_t ω^{7(tk) + tk'}     (by star_omega8_pow_mul_pow)
= ∑_t ω^{t(7k + k')}      (factoring out t)
```

This transforms the inner product computation into a roots of unity sum.
-/

structure SumStarOmega8ProdCert where
  deriving Repr

/-- Verification predicate: sum of conjugate products equals sum of powers. -/
@[simp] def SumStarOmega8ProdCert.verified (_c : SumStarOmega8ProdCert) : Prop :=
  ∀ k k' : Fin 8,
    Finset.univ.sum (fun t : Fin 8 => star (omega8 ^ (t.val * k.val)) * omega8 ^ (t.val * k'.val)) =
    Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * (7 * k.val + k'.val)))

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem SumStarOmega8ProdCert.verified_any (c : SumStarOmega8ProdCert) :
    SumStarOmega8ProdCert.verified c := by
  intro k k'
  exact sum_star_omega8_pow_prod k k'

end SumStarOmega8Prod
end Verification
end IndisputableMonolith
