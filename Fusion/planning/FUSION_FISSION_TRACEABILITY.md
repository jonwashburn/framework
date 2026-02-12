## Fusion + Fission Traceability (Theorem → Asset Map)

**Owner:** Jonathan Washburn  
**Date:** 2026-01-19  

This document links formally verified Lean theorems to external deliverables (papers, patents, specs).\n+
---

### 1. Fusion module mapping (existing)

| Lean theorem | File | External asset | Notes |
|---|---|---|---|
| `phi_more_robust` | `Fusion/JitterRobustness.lean` | Patent: jitter-robust φ scheduling | Quadratic vs linear degradation |
| `phi_interference_bound_exists` | `Fusion/InterferenceBound.lean` | Paper: Golden-ratio pulse sequencing robustness | Interference ratio bound |
| `local_descent_link` | `Fusion/LocalDescent.lean` | Patent: certified symmetry control loops | Ledger descent ⇒ proxy improvement |
| `magicFavorable_decreases_distance` | `Fusion/ReactionNetwork.lean` | Patent: graph-theoretic fuel optimization | Stability improvement monotonicity |
| `r_process_peaks_at_magic_N` | `Fusion/Nucleosynthesis.lean` | Paper: attractor nucleosynthesis | Waiting points at magic N |

---

### 2. Fission module mapping (new)

| Lean theorem | File | Intended asset | Notes |
|---|---|---|---|
| `splitCost_zero_of_doublyMagic` | `Fission/FragmentAttractors.lean` | Paper: fission yield peaks via split attractors | Baseline (no penalty term) |
| `splitCost_minimal_of_doublyMagic` | `Fission/FragmentAttractors.lean` | Paper/patent: magic-fragment minimizing splits | Will be strengthened with penalties |
| `energyProxy_sn132_le_symmetric_of_imbalance` | `Fission/FragmentAttractors.lean` | Paper: fission yield peaks (tradeoff inequality) | Concrete condition for Sn-132 split to dominate a symmetric baseline |

---

### 3. Planned additions (placeholders)

| Planned theorem | Planned file | Intended asset |
|---|---|---|
| “derived magic numbers reproduce observed list” | `Nuclear/MagicNumbersDerivation.lean` | Paper: deriving magic numbers from ledger topology |
| “fission cycling preserves r-process peaks” | `Astrophysics/FissionCycling.lean` | Paper: peak robustness under fission cycling |

