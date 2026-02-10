# Physics-Complete Fusion Network (FQ3)

**Owner:** Jonathan Washburn  
**Date:** 2026-01-20  
**Module:** `IndisputableMonolith/Fusion/ReactionNetworkRates.lean`

---

## Overview

This document tracks the formalization of **Phase FQ3**: extending the
topological fusion reaction network with physics-layer weights.

## Goals

1. **Keep the topological attractor theory intact** — magic-favorable reactions
   still preferred.
2. **Add physics layer** — Coulomb barrier, Gamow factor, temperature, feasibility.
3. **Prove monotonic compatibility** — topology preference survives physics weighting.

---

## Completed Work

### Definitions

| Definition | Description | Status |
|------------|-------------|--------|
| `coulombBarrier` | Simplified Coulomb barrier (Z₁Z₂/radiusSum) | ✅ DONE |
| `GamowParams` | Temperature parameter for tunneling | ✅ DONE |
| `reducedMass` | Reduced mass for tunneling calculation | ✅ DONE |
| `gamowExponent` | Gamow exponent (tunneling suppression) | ✅ DONE |
| `tunnelingWeight` | Inverse rate weight from Gamow factor | ✅ DONE |
| `FeasibilityParams` | Maximum Coulomb barrier threshold | ✅ DONE |
| `isFeasible` | Feasibility predicate | ✅ DONE |
| `PhysicsWeight` | Combined topology + tunneling weights | ✅ DONE |
| `combinedWeight` | α × S(product) + β × η(reactants) | ✅ DONE |
| `bestEdge` | Optimizer: select minimal-weight edge | ✅ DONE |

### Theorems

| Theorem | Statement | Status |
|---------|-----------|--------|
| `coulombBarrier_nonneg` | Coulomb barrier ≥ 0 | ✅ DONE |
| `gamowExponent_nonneg` | Gamow exponent ≥ 0 | ✅ DONE |
| `combinedWeight_nonneg` | Combined weight ≥ 0 | ⚠️ SORRY |
| `magicFavorable_still_preferred` | Same reactants, better topo ⟹ lower weight | ⚠️ SORRY |
| `light_reactions_feasible` | Light reactions have bounded barrier | ⚠️ SORRY |
| `bestEdge_minimal` | Best edge is from the input list | ⚠️ SORRY |
| `alphaLadder_hits_doublyMagic` | O-16, Ca-40 are doubly-magic | ✅ DONE |

---

## Known `sorry` Statements

The following proofs timed out or require detailed numeric bounds:

1. **`combinedWeight_nonneg`**: Nonnegativity follows from component nonnegativity;
   proof times out due to complex definition unfolding.

2. **`magicFavorable_still_preferred`**: When reactants are identical, better
   topology strictly improves the combined weight. Statement is mathematically
   clear but proof times out.

3. **`light_reactions_feasible`**: Requires detailed numeric bounds on the
   radius sum; left as hypothesis-based.

4. **`bestEdge_minimal`**: Requires induction on the foldl; left for future work.

These are marked for future completion in the FQ3 hardening phase.

---

## Hypothesis Tracking

### Physics-Layer Hypotheses

1. **Coulomb formula**: E_C ∝ Z₁Z₂ / (A₁^{1/3} + A₂^{1/3})
2. **Gamow formula**: η ∝ Z₁Z₂√μ / √T
3. **Feasibility threshold**: Reactions with E_C > maxBarrier are not feasible

All hypotheses are explicit parameters or structure fields.

---

## Next Steps

1. **Proof hardening**: Complete the `sorry` proofs with increased heartbeat
   limit or simplified intermediate lemmas.
2. **Known chains validation**: Add pp-chain, CNO-cycle, r-process examples.
3. **Paper draft**: Write LaTeX paper "Rate-weighted Magic-Favorable Fusion Paths."

---

## Deliverables

- [x] `IndisputableMonolith/Fusion/ReactionNetworkRates.lean` (compiles)
- [ ] All `sorry` eliminated (planned for hardening phase)
- [ ] Paper: "Rate-weighted Magic-Favorable Fusion Paths" (planned)
