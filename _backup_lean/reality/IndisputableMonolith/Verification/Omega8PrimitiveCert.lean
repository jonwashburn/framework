import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith
namespace Verification
namespace Omega8Primitive

open IndisputableMonolith.LightLanguage.Basis

/-!
# Omega8 Primitive Root Certificate

This certificate proves that ω = e^{-2πi/8} is a *primitive* 8th root of unity,
meaning ω^k ≠ 1 for all 0 < k < 8.

## Key Result

For all k ∈ {1, 2, 3, 4, 5, 6, 7}: `omega8 ^ k ≠ 1`

## Why this matters for the certificate chain

Primitivity is essential for DFT properties:

1. **Non-degeneracy**: ω^k for k = 0..7 are all distinct
2. **Roots of Unity Sum**: ∑_{t=0}^{7} ω^{tk} = 0 for k ≠ 0 relies on ω^k ≠ 1
3. **DFT Orthogonality**: Column orthonormality depends on non-degenerate roots

## Mathematical Content

The proof uses:
- ω = exp(-iπ/4)
- exp(z) = 1 iff z = 2πin for some integer n
- For 0 < k < 8: k·(-π/4) ≠ 2πn for any integer n (since k/8 ∉ ℤ)

## Geometric Interpretation

The 8th roots of unity ω^k for k = 0..7 form a regular octagon on the unit circle.
Primitivity means ω^k returns to 1 *only* at k = 0 (mod 8), not before.
-/

structure Omega8PrimitiveCert where
  deriving Repr

/-- Verification predicate: ω is a primitive 8th root of unity. -/
@[simp] def Omega8PrimitiveCert.verified (_c : Omega8PrimitiveCert) : Prop :=
  ∀ k : ℕ, 0 < k → k < 8 → omega8 ^ k ≠ 1

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem Omega8PrimitiveCert.verified_any (c : Omega8PrimitiveCert) :
    Omega8PrimitiveCert.verified c := by
  intro k hpos hlt
  exact omega8_pow_ne_one k hpos hlt

end Omega8Primitive
end Verification
end IndisputableMonolith
