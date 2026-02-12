import Hodge.Analytic.Integration.VolumeForm
import Hodge.Analytic.Integration.TopFormIntegral
import Hodge.Analytic.Integration.L2Inner
import Hodge.Analytic.Integration.ExtDerivCohomology
import Hodge.Analytic.Integration.StokesTheorem
import Hodge.Analytic.Integration.PairingConnection
import Hodge.Analytic.Integration.HausdorffMeasure
import Hodge.Analytic.Integration.Compatibility

/-!
# Integration Theory for Kähler Manifolds

This module provides the integration infrastructure for the Hodge Conjecture formalization.

## Overview

Integration on a compact Kähler manifold X of complex dimension n involves:
1. **Volume forms**: The canonical (2n)-form ω^n / n! induced by the Kähler metric
2. **Top-form integration**: The functional ∫_X : Ω^{2n}(X) → ℝ
3. **Intersection pairing**: ⟨α, β⟩ = ∫_X α ∧ β for complementary-degree forms

## Files

* `VolumeForm.lean`: Defines `kahlerVolumeForm`, `kahlerMeasure`, `totalVolume`
* `TopFormIntegral.lean`: Defines `topFormIntegral_real'`, `intersectionPairing`

## Sprint Status

### Sprint 1 (Current)
- [x] Directory structure created
- [x] Type signatures for all definitions
- [x] Key theorems stated (with sorry bodies)
- [x] Module file created

### Sprint 2 (Upcoming)
- [ ] Implement `kahlerVolumeForm` using iterated wedge
- [ ] Implement `topFormIntegral_real'` using Mathlib integration
- [ ] Update `Microstructure.lean` to use new definitions
- [ ] Prove linearity theorems

## Mathematical Background

### Volume Form
On a Kähler manifold (X, ω) of complex dimension n:
- The Kähler form ω is a closed real (1,1)-form
- ω^n is a nowhere-vanishing (2n)-form (Wirtinger)
- vol = ω^n / n! is the Riemannian volume form

### Integration
For a top-form η on compact X:
- ∫_X η = ∫_X f dμ where η = f · vol
- μ is the Riemannian measure (= Hausdorff measure H^{2n})
- |∫_X η| ≤ vol(X) · ‖η‖_∞

### Intersection Pairing (Poincaré Duality)
For α ∈ Ω^{2p}(X) and β ∈ Ω^{2(n-p)}(X):
- ⟨α, β⟩ = ∫_X α ∧ β
- This descends to a perfect pairing on cohomology (Poincaré duality)
- Key for cycle class definitions

## References

* [Griffiths-Harris, "Principles of Algebraic Geometry", Chapter 0]
* [Voisin, "Hodge Theory and Complex Algebraic Geometry I", Chapter 5]
* [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Chapter 4]
* [Federer, "Geometric Measure Theory", Chapter 4]

-/
