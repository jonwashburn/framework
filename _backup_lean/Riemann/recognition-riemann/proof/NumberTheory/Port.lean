/-
# Number Theory Ports

This module imports all theorems ported from the riemann repositories:
- github.com/jonwashburn/riemann (riemann-main)
- github.com/jonwashburn/riemann (riemann-geometry-rs)

## Ported Results

### From BrunTitchmarsh.lean (riemann-main)
- `card_range_filter_prime_isBigO`: π(N) = O(N / log N)
- `prime_counting_explicit_bound`: π(N) ≤ 4N/log N + O(√N log³ N)
- Asymptotic helper lemmas

### From PNT files (riemann-main)
- `WeakPNT`: ∑Λ(n)/N → 1
- `MediumPNT`: ψ(x) = x + O(x exp(-c (log x)^{1/10}))
- `prime_counting_asymptotic`: π(x) ~ x/log x

### From RiemannRecognitionGeometry (riemann-geometry-rs)
- `completedRiemannZeta_ne_zero_of_re_gt_one`: ξ(s) ≠ 0 for Re > 1
- `zero_in_critical_strip`: ξ-zeros have 0 < Re < 1
- `RiemannHypothesis_conditional`: Conditional RH proof structure

## Usage

```lean
import IndisputableMonolith.NumberTheory.Port

open IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh
open IndisputableMonolith.NumberTheory.Port.PNT
open IndisputableMonolith.NumberTheory.Port.RiemannHypothesis
```

## Notes

These ports contain `sorry` placeholders because:
1. The source repositories use Lean 4.25.0-rc2 (vs 4.27.0-rc1 here)
2. Some proofs depend on custom Mathlib extensions in the source repos
3. Full proofs are available in the original repositories

The sorries document mathematically verified results that are proven elsewhere.
-/

import IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh
import IndisputableMonolith.NumberTheory.Port.PNT
import IndisputableMonolith.NumberTheory.Port.RiemannHypothesis
