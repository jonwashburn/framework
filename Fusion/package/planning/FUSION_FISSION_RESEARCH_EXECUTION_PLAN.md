## Fusion + Fission: Open Questions & Derivation Expansion — Execution Plan

**Owner:** Jonathan Washburn  
**Date:** 2026-01-19  
**Context:** `planning/FUSION_THEORY_IMPLEMENTATION_PLAN.md` is complete. This plan covers the *next* work: resolving remaining open questions and extending the same formal machinery to **fission**.

---

### 0. Snapshot (what we already have)

- **Fusion (formalized, machine-checked):**
  - `IndisputableMonolith/Fusion/LocalDescent.lean` (local descent link + control corollaries)
  - `IndisputableMonolith/Fusion/InterferenceBound.lean` (φ interference bounds)
  - `IndisputableMonolith/Fusion/JitterRobustness.lean` (quadratic jitter robustness vs linear)
  - `IndisputableMonolith/Fusion/NuclearBridge.lean` (magic distance + stability distance)
  - `IndisputableMonolith/Fusion/BindingEnergy.lean` (shell correction proxy + SEMF wrapper)
  - `IndisputableMonolith/Fusion/ReactionNetwork.lean` (fusion graph + attractor properties)
  - `IndisputableMonolith/Fusion/Nucleosynthesis.lean` (+ `Astrophysics/NucleosynthesisWaitingPoints.lean`) (waiting points + peaks)

- **IP/papers already written from this work:**
  - Patents: φ scheduling + graph fuel optimization + certified symmetry control.
  - Papers: Golden-ratio pulse robustness; topological shell corrections; attractor nucleosynthesis.

---

### 1. Guiding principles (do-it-right constraints)

- **Formal-first:** any “core claim” must be stated precisely and proved in Lean 4 (no `sorry`).
- **Minimize rebuild cost:** build targeted modules only (e.g. `lake build IndisputableMonolith.Fusion.ReactionNetwork`).
- **Traceability:** every new theorem or hypothesis must be tracked in a status doc and mapped to deliverables (paper/patent/spec).
- **No silent assumptions:** if we need a physical premise (rates, feasibility, thermodynamics), it becomes an explicit hypothesis, recorded and audited.
- **Two-layer model:**
  - **Layer A (discrete/topological invariants):** stability distance, attractor proofs, monotone measures.
  - **Layer B (physics instantiation):** mapping from real diagnostics / nuclear data into Layer A.

---

### 2. Master question list (what this plan resolves)

#### 2.1 Remaining fusion questions

- **FQ1 — Derive magic numbers (don’t assume the list):** produce a ledger-topology theorem that outputs the magic sequence.
- **FQ2 — Make shell correction quantitative from RS:** derive coupling scale(s) and scaling laws instead of “fit κ”.
- **FQ3 — Physics-complete reaction network:** add feasibility/rate weights (Coulomb barrier / Gamow factor / temperature).
- **FQ4 — Close the loop to real ICF observables:** connect `Symmetry Ledger` variables to diagnostics and hydro symmetry.
- **FQ5 — Generalize φ robustness:** correlated jitter/drift, amplitude noise, quantized timing, multi-channel constraints.
- **FQ6 — Certified implementations:** produce executable artifacts + test vectors + interface specs for facility deployment.

#### 2.2 Fission derivations to add

- **FI1 — Fragment yield peaks via “split attractors”:** predict yield peaks from a split-graph cost functional (magic fragments emerge).
- **FI2 — Barrier/deformation landscape from shell proxy:** qualitative + semi-quantitative barrier shaping using stability distance.
- **FI3 — r-process fission cycling invariants:** show peak structure persists under recycling.
- **FI4 — Spontaneous-fission stability ranking:** prove monotone trends (higher distance → lower barrier proxy) under explicit hypotheses.

---

### 3. Deliverables map (Lean + docs + publications)

| Work item | Lean artifacts (target) | Docs (target) | Publication output |
|---|---|---|---|
| FQ1 | `Nuclear/MagicNumbersDerivation.lean` | `planning/MAGIC_NUMBER_DERIVATION_STATUS.md` | Paper: “Deriving Magic Numbers from Ledger Topology” |
| FQ2 | extend `Fusion/BindingEnergy.lean` + `Nuclear/ShellCoupling.lean` | `planning/SHELL_COUPLING_NOTES.md` | Paper: “Quantitative Shell Corrections from RS” |
| FQ3 | `Fusion/ReactionNetworkRates.lean` | `planning/FUSION_NETWORK_PHYSICS_LAYER.md` | Paper/tech note: “Rate-weighted Magic-Favorable Fusion Paths” |
| FQ4 | `Fusion/DiagnosticsBridge.lean` | `planning/ICF_DIAGNOSTIC_MAPPING.md` | Paper: “Certified Symmetry Control with Diagnostics Traceability” |
| FQ5 | extend `Fusion/JitterRobustness.lean` | `planning/PHI_SCHEDULING_NOISE_MODEL.md` | Paper: “φ Scheduling Under Correlated Noise” |
| FQ6 | `Fusion/Executable/…` + test vectors | `papers/tex/Fusion_Software_Functional_Specification.tex` (update) | Deployment guide + (optional) patent continuations |
| FI1 | `Fission/FragmentAttractors.lean` | `planning/FISSION_FRAGMENT_YIELD_PLAN.md` | Paper: “Topological Explanation of Fission Yield Peaks” |
| FI2 | `Fission/BarrierLandscape.lean` | `planning/FISSION_BARRIER_NOTES.md` | Paper: “Shell-Topology Control of Fission Barriers” |
| FI3 | `Astrophysics/FissionCycling.lean` | `planning/RPROCESS_FISSION_CYCLING.md` | Paper: “Peak Robustness Under Fission Cycling” |
| FI4 | `Fission/SpontaneousFissionRanking.lean` | `planning/SF_RANKING_ASSUMPTIONS.md` | Paper/tech note: “A Certified Proxy for Fission Half-life Ranking” |

---

### 4. Execution phases (ordered, with quality gates)

#### Phase 0 — Setup: status tracking + audit framework (1–2 sessions)

- **Goal:** create the scaffolding to prevent drift and keep hypotheses explicit.
- **Tasks:**
  - Create `IndisputableMonolith/Fission/` directory and `IndisputableMonolith/Fission/THEORY_STATUS.md`.
  - Add a new audit doc: `planning/FISSION_AUDIT_REPORT.md` (hypotheses, axioms, sorries).
  - Establish a “theorem-to-asset” table (Lean theorem ↔ patent claim / paper section / spec requirement).
- **Quality gate:**
  - No `sorry` in newly created Fission modules.
  - Audit docs exist and are updated with every hypothesis.

#### Phase 1 — FQ1: Derive magic numbers from ledger topology (foundation) (multi-week, foundational)

- **Goal:** replace “magic numbers are a list” with “magic numbers are a theorem.”
- **Key idea:** define a ledger topology object and a stability functional whose local/global maxima occur at the observed sequence.
- **Tasks:**
  - Specify the minimal ledger axioms needed (keep them small and testable).
  - Define “ledger shell closure” as a formal property.
  - Prove that closure points generate the sequence (or generate a family that includes it with tight constraints).
  - Provide a compatibility lemma: derived set implies existing `Nuclear.MagicNumbers.isMagic`.
- **Quality gate:**
  - A Lean theorem exporting the sequence (and optionally its next predictions).
  - A proof that the derived sequence reproduces the current one up to 126.

#### Phase 2 — FQ2: Quantitative shell correction coupling (κ) (multi-week)

- **Goal:** move from qualitative “-S(Z,N)” to quantitative “κ(A,Z,N)” derived from RS scaling laws.
- **Tasks:**
  - Split the problem:
    - **(2a)** derive dimensionless scaling (how shell gap changes with A).
    - **(2b)** derive energy scale anchor (κ in MeV) from RS constants.
  - Update `Fusion/BindingEnergy.lean` to support κ as a function (not only constant).
  - Prove qualitative invariants remain true under κ(A).
- **Quality gate:**
  - κ is derived from stated constants/hypotheses, not “fit and forget.”
  - Theorems like “max at doubly-magic” still hold.

#### Phase 3 — FQ3: Physics-complete fusion network (rates + feasibility) (multi-week)

- **Goal:** keep the attractor theory, but add a “physics layer” that selects *realizable* edges and ranks them by rate.
- **Tasks:**
  - Define a feasibility predicate (Coulomb barrier, temperature, conservation, endo/exothermic).
  - Define a rate weight model (e.g., simplified Gamow factor) as a hypothesis-backed function.
  - Prove monotonic compatibility: Magic-favorable edges remain favored under broad conditions.
  - Implement an optimizer that combines:
    - stability improvement (topology)
    - feasibility + rate (physics)
- **Quality gate:**
  - The optimizer produces physically meaningful outputs for known chains (pp-chain, triple-α, α-ladder).
  - All new assumptions documented.

#### Phase 4 — FQ4: Diagnostics bridge for certified symmetry control (multi-week)

- **Goal:** connect the certified `Symmetry Ledger` and `LocalDescent` theorems to real measured symmetry observables.
- **Tasks:**
  - Define a mapping from diagnostics (e.g., low-order spherical harmonic modes) to ratio vector `r`.
  - Prove: within calibration envelope, decreasing ledger implies decreasing an observable asymmetry proxy.
  - Add certificate format that includes diagnostic metadata and calibration version.
- **Quality gate:**
  - A “traceability theorem”: PASS certificate implies a reduction in a stated observable proxy under explicit hypotheses.

#### Phase 5 — FQ5: Generalize φ scheduling robustness (multi-week)

- **Goal:** extend beyond i.i.d. jitter to the real noise stack.
- **Tasks:**
  - Correlated jitter model (bounded covariance).
  - Drift + calibration error.
  - Quantized timing (hardware resolution).
  - Multi-channel scheduling (many beams, coupled constraints).
  - Prove “quadratic (or near-quadratic) advantage” conditions.
- **Quality gate:**
  - A theorem list: which noise models preserve quadratic advantage and under what bounds.

#### Phase 6 — FQ6: Certified executable implementations (engineering hardening) (multi-week)

- **Goal:** produce deployment-grade artifacts (APIs + test vectors + trace logs).
- **Tasks:**
  - Define stable interfaces for each module (inputs/outputs + units).
  - Create deterministic test vectors derived from Lean definitions (golden files).
  - Provide “certificate bundles” (JSON) that correspond to Lean-checkable statements.
  - Update `papers/tex/Fusion_Software_Functional_Specification.tex` to Version 1.1 with the new interfaces.
- **Quality gate:**
  - Reproducible test suite: given inputs, outputs match spec and certificate logs verify.

#### Phase 7 — FI1: Fission fragment yield peaks as split-attractors (multi-week)

- **Goal:** derive yield peaks from a split-graph cost functional.
- **Core model:** a fission event is a hyperedge:
  - parent `(Z,N)` -> `{(Z1,N1),(Z2,N2)}` with conservation.
- **Tasks:**
  - Define split edges with conservation proofs.
  - Define split cost:
    - stability term: S(fragment1)+S(fragment2)
    - plus a minimal penalty for Coulomb/surface (explicit hypothesis)
  - Prove: minimizing split cost selects fragments near magic closures.
- **Quality gate:**
  - A Lean theorem: under stated penalty bounds, global minima include (or concentrate near) magic fragments.

#### Phase 8 — FI2: Barrier/deformation landscape (multi-week)

- **Goal:** formalize qualitative statements about fission barriers shaped by shell closures.
- **Tasks:**
  - Define a deformation parameter and a barrier proxy functional.
  - Add a shell term from stability distance.
  - Prove monotone claims (closures raise barrier locally) under explicit hypotheses.
- **Quality gate:**
  - Theorems that explain “island of stability” qualitatively from the shell term.

#### Phase 9 — FI3: r-process fission cycling invariants (multi-week)

- **Goal:** show that adding fission recycling does not destroy magic waiting-point peaks.
- **Tasks:**
  - Extend nucleosynthesis graph with fission edges.
  - Define an invariant measure showing peaks persist.
  - Prove: waiting points remain fixed points / attractors under cycling.
- **Quality gate:**
  - A Lean theorem that peak locations are stable under the extended dynamics.

#### Phase 10 — FI4: Spontaneous fission stability ranking (multi-week)

- **Goal:** produce a certified proxy for comparing half-life trends.
- **Tasks:**
  - Define a monotone “barrier proxy” based on stability distance and deformation cost.
  - Prove: increasing S increases proxy instability under explicit assumptions.
  - Provide ranking algorithm + correctness theorem.
- **Quality gate:**
  - Proven monotonicity and soundness of the ranking proxy.

#### Phase 11 — Packaging: papers + patents + integration narrative (continuous)

- **Goal:** turn theorems into publishable and protectable assets.
- **Tasks:**
  - For each phase, write/update a corresponding LaTeX paper section and a claim set.
  - Maintain a single “asset ledger” doc: `planning/FUSION_FISSION_IP_ASSETS.md`.
- **Quality gate:**
  - Every key theorem appears in at least one external artifact (paper/patent/spec).

---

### 5. Risk register + mitigations

- **R1: Magic-number derivation might require stronger axioms than desired.**
  - Mitigation: start with a minimal ledger object that reproduces *structure* (closure points) and refine; keep alternate axiom sets side-by-side.

- **R2: Physics-complete rate model introduces many assumptions.**
  - Mitigation: isolate physics layer behind a small interface; keep the topological layer clean.

- **R3: Diagnostics bridge depends on facility-specific calibration.**
  - Mitigation: formalize calibration as a certificate (versioned assumptions) and keep proofs conditional.

- **R4: Fission models can explode in complexity.**
  - Mitigation: begin with “split attractor” theory (FI1) which is discrete and proof-friendly; only then add deformation/barriers.

---

### 6. Success criteria (definition of done)

- **Mathematical:**
  - All new Lean modules build with **no `sorry`**.
  - All new hypotheses are cataloged in audit docs.

- **Scientific:**
  - Magic numbers are derived (or tightly constrained) by ledger topology.
  - Fusion optimizer produces physically filtered paths.
  - Fission yield peaks emerge from split-attractor theory.

- **Engineering:**
  - Executable interfaces exist with test vectors.
  - Certificates/logs provide auditability.

---

### 7. Immediate next actions (first concrete steps)

- Create Phase 0 scaffolding:
  - `IndisputableMonolith/Fission/` + `IndisputableMonolith/Fission/THEORY_STATUS.md`
  - `planning/FISSION_AUDIT_REPORT.md`
  - `planning/MAGIC_NUMBER_DERIVATION_STATUS.md`

- Decide which “foundation-first” track to run in parallel:
  - Track A: FQ1 (magic number derivation)
  - Track B: FI1 (fission fragment attractors)

