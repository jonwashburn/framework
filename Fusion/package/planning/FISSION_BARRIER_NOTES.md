## FI2 Notes — Fission Barrier / Deformation Landscape

**Owner:** Jonathan Washburn  
**Date:** 2026-01-19  
**Related execution plan:** `planning/FUSION_FISSION_RESEARCH_EXECUTION_PLAN.md` (Phase 8 / FI2)

This file tracks the FI2 work: connecting shell/magic structure (via Stability Distance)
to a proxy fission barrier landscape over an abstract deformation coordinate.

---

### 1. Current code status

- **Lean scaffold:** `IndisputableMonolith/Fission/BarrierLandscape.lean`
  - Defines `BarrierModel` with:
    - `baseBarrier cfg q` (physics-layer input, assumed nonnegative)
    - `shellCoupling ≥ 0`
  - Defines:
    - `shellTension = shellCoupling * stabilityDistance`
    - `totalBarrier = baseBarrier + shellTension`
  - Proves nonnegativity of `shellTension` and `totalBarrier`

This is intentionally minimal: it creates the *surface* for later theorems without
hardcoding any physics parameters.

---

### 2. Next targets (FI2)

#### FI2.1 — Local barrier shaping near shell closures

Add hypotheses that encode “shell closures raise barrier locally” or “create local minima”
in a deformation-dependent energy, and prove:
- If `cfg` is doubly-magic, the shell term is minimized (`stabilityDistance cfg = 0`)
- Under mild assumptions, `totalBarrier` achieves a locally favorable profile near closures

#### FI2.2 — “Island of stability” qualitative theorem (proxy)

Introduce a `SuperheavyCandidate` region and show:
- closures (small stability distance) reduce the shell tension term enough to offset baseline instability
- yields qualitative ranking predictions under explicit assumptions

---

### 3. Hypothesis tracking

All deformation physics assumptions must be recorded in:
- `planning/FISSION_AUDIT_REPORT.md`

