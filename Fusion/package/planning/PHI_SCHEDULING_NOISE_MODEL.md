# φ Scheduling Under Generalized Noise (FQ5)

**Owner:** Jonathan Washburn  
**Date:** 2026-01-20  
**Module:** `IndisputableMonolith/Fusion/GeneralizedJitter.lean`

---

## Overview

This document tracks the formalization of **Phase FQ5**: extending the basic
jitter robustness theory to realistic noise stacks.

## Goals

Prove conditions under which "quadratic advantage" of φ-scheduling is preserved.

---

## Noise Models Formalized

### 1. Correlated Jitter

| Structure | Description |
|-----------|-------------|
| `CorrelatedJitterModel` | n channels with marginal amplitudes and covariance bound |
| `maxMarginal` | Maximum marginal amplitude |
| `effectiveAmplitude` | Effective amplitude accounting for correlation |

**Key Theorem**: `quadratic_advantage_under_correlation`
- If ρ × (n-1) ≤ 1, then effective amplitude ≤ maxMarginal × √n × √2

### 2. Drift + Calibration Error

| Structure | Description |
|-----------|-------------|
| `DriftModel` | Drift rate + calibration offset |
| `CombinedNoiseModel` | Jitter + drift |
| `totalDriftError` | Total drift at time t |
| `totalNoiseAmplitude` | Combined jitter + drift |

**Key Theorem**: `quadratic_with_bounded_drift`
- If drift × T ≤ jitter, then total noise ≤ 2 × jitter

### 3. Quantized Timing

| Structure | Description |
|-----------|-------------|
| `QuantizedTimingModel` | Resolution + quantization error |
| `effectiveJitterWithQuantization` | Jitter + quantization |

**Key Theorem**: `quadratic_with_quantization`
- If quantization ≤ jitter, then effective jitter ≤ 2 × jitter

### 4. Multi-Channel Scheduling

| Structure | Description |
|-----------|-------------|
| `MultiChannelConfig` | n channels, φ-scheduled flag, phase constraint |

**Key Theorem**: `multiChannel_interference_scaling`
- Independent channels scale as √n × single-channel

---

## Main Theorem (FQ5)

`quadratic_advantage_conditions`: Quadratic advantage is preserved under:

1. **Bounded correlation**: ρ × (n-1) ≤ 1
2. **Bounded drift**: drift × T ≤ jitter amplitude
3. **Small quantization**: quantization error ≤ jitter amplitude
4. **Independent multi-channel**: each channel φ-scheduled

Under these conditions, degradation scales as O(ε²) rather than O(ε).

---

## Completed Work

### Definitions (all ✅ DONE)

- `CorrelatedJitterModel`, `maxMarginal`, `effectiveAmplitude`
- `DriftModel`, `CombinedNoiseModel`, `totalDriftError`, `totalNoiseAmplitude`
- `QuantizedTimingModel`, `effectiveJitterWithQuantization`
- `MultiChannelConfig`

### Theorems (all ✅ DONE)

- `effectiveAmplitude_nonneg`
- `quadratic_advantage_under_correlation`
- `totalDriftError_nonneg`
- `quadratic_with_bounded_drift`
- `quantizationError_le_half_resolution`
- `quadratic_with_quantization`
- `multiChannel_interference_scaling`
- `multiChannel_quadratic_advantage`
- `quadratic_advantage_conditions` (main theorem)

---

## No `sorry` Statements

All proofs in this module are complete.

---

## Next Steps

1. **Amplitude sensitivity**: Add theorems for amplitude noise (not just timing).
2. **Correlated multi-channel**: Handle coupled constraints between channels.
3. **Paper draft**: Write "φ Scheduling Under Correlated Noise."

---

## Deliverables

- [x] `IndisputableMonolith/Fusion/GeneralizedJitter.lean` (compiles, no sorry)
- [ ] Paper: "φ Scheduling Under Correlated Noise" (planned)
