# Fission Theory Status (Formalization)

**Owner:** Jonathan Washburn  
**Status:** in progress  
**Last updated:** 2026-01-19  

This file tracks proof status for the `IndisputableMonolith/Fission/*` modules.

## Module: `IndisputableMonolith/Fission/FragmentAttractors.lean`

### Definitions

- **`SplitEdge`**: fission split edge `parent -> (fragA, fragB)` with Z/N conservation — **DONE**
- **`splitCost`**: baseline split cost functional `stabilityDistance fragA + stabilityDistance fragB` — **DONE**
- **`totalSplitCost`**: penalty-augmented split cost `(splitCost : ℝ) + penalty` — **DONE**
- **`SplitPenalty` / `totalSplitCostP`**: structured nonnegative penalty model + induced cost — **DONE**

### Theorems

- **`splitCost_zero_of_doublyMagic`**: if both fragments are doubly-magic, split cost is 0 — **DONE**
- **`splitCost_minimal_of_doublyMagic`**: such a split is cost-minimal (among splits of same parent) — **DONE**
- **`totalSplitCost_nonneg`**: total split cost is nonnegative under penalty nonnegativity — **DONE**
- **`totalSplitCost_minimal_of_doublyMagic`**: if penalty is nonnegative and vanishes on a doubly-magic split, that split is cost-minimal — **DONE**
- **`totalSplitCostP_nonneg`**: structured-penalty nonnegativity — **DONE**
- **`totalSplitCostP_minimal_of_doublyMagic`**: structured-penalty minimality (penalty vanishes on the split) — **DONE**
- **`energyProxy`**: weighted objective `penalty + lam * splitCost` — **DONE**
- **`energyProxy_le_of_penalty_le`**: generic comparison lemma for weighted objective — **DONE**
- **`splitCost_nonneg`**: split cost is nonnegative — **DONE**
- **`splitCost_sn132_lt_symmetric`**: proxy-metric example ranking a Sn-132 split over a symmetric split for a representative parent — **DONE**
- **`energyProxy_sn132_le_symmetric`**: Sn-132 split beats symmetric split when penalty disadvantage is bounded by shell weight — **DONE**
- **`imbalancePenalty`**: explicit mass-imbalance penalty (symmetric-favoring) — **DONE**
- **`imbalancePenaltyModel`**: packaged `SplitPenalty` instance for imbalance penalty (requires `k ≥ 0`) — **DONE**
- **`energyProxy_sn132_le_symmetric_of_imbalance`**: concrete inequality condition for Sn-132 to beat symmetric under imbalance penalty — **DONE**
- **`chargeImbalancePenalty`**: explicit Z-asymmetry penalty (symmetric-favoring) — **DONE**
- **`energyProxy_sn132_le_symmetric_of_chargeImbalance`**: Sn-132 dominance condition under Z-asymmetry penalty — **DONE**

### Notes / next steps (FI1 continuation)

- Add a **penalty term** (Coulomb/surface proxy) and prove “magic-fragment minima” under explicit boundedness hypotheses.
- Add a **worked example** split (e.g., a heavy fragment near `(50,82)`), expressed as a theorem about minimizing `splitCost` under constraints.
- Extend to **yield concentration** statements (probability mass concentrates near low-cost splits) under an explicit sampling model.

## Module: `IndisputableMonolith/Fission/BarrierLandscape.lean`

### Definitions

- **`BarrierModel`**: baseline barrier profile + nonnegative shell coupling — **DONE**
- **`shellTension`**: shell/topology tension term `shellCoupling * stabilityDistance` — **DONE**
- **`totalBarrier`**: baseline + shell tension — **DONE**

### Theorems

- **`shellTension_nonneg`** — **DONE**
- **`totalBarrier_nonneg`** — **DONE**

### Notes / next steps (FI2 continuation)

- Add deformation-shaping hypotheses and prove qualitative "closure improves barrier" statements.
- Connect to a proxy "island of stability" ranking under explicit assumptions.

## Module: `IndisputableMonolith/Fission/SpontaneousFissionRanking.lean`

### Definitions

- **`SFRankingModel`**: barrier scale (positive) + physics-layer baseline (nonnegative) — **DONE**
- **`barrierProxy`**: barrier proxy = baseline + barrierScale × (maxDist − stabilityDistance) — **DONE**
- **`instabilityProxy`**: alternative form (higher stabilityDistance → higher instability) — **DONE**
- **`isMoreStable`**: ranking predicate comparing barrier proxies — **DONE**

### Theorems

- **`barrierProxy_monotone`**: lower stabilityDistance ⟹ higher barrier proxy (under same baseline) — **DONE**
- **`doublyMagic_max_barrier`**: doubly-magic nuclei achieve maximal barrier proxy — **DONE**
- **`ranking_by_distance`**: ranking by stability distance under equal baseline — **DONE**
- **`cf252_stabilityDistance`**: concrete value for Cf-252 — **DONE**
- **`fm256_stabilityDistance`**: concrete value for Fm-256 — **DONE**
- **`cf252_more_stable_than_fm256_cond`**: Cf-252 more stable than Fm-256 under equal baseline — **DONE**
- **`ranking_soundness`**: soundness statement for the proxy — **DONE**

### Notes / next steps (FI4 continuation)

- Incorporate Z²/A-based baseline to make the model more physically realistic.
- Add explicit prediction examples for superheavy elements (e.g., Og-294).