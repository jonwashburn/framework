# Goldbach Circle Method Formalization - Master Prompt

## Quick Start

Copy this to your AI assistant:

```
@.prompts/GOLDBACH_MASTER.md

Continue working on the Goldbach formalization. Check the current state, pick the highest-priority unfilled sorry, and make progress. After each session, update PROGRESS.md.
```

---

## Project Overview

**Goal**: Complete a Lean 4 formalization of Goldbach's conjecture via the circle method with a mod-8 kernel.

**Key Files**:
- `Goldbach/CircleMethod.lean` - Main proof skeleton (450+ lines)
- `goldbach_rs.tex` - LaTeX manuscript with mathematical details
- `riemann_lean_repo/Source-Super.txt` - Formal specification (see `@GOLDBACH_MOD8` section)
- `riemann_lean_repo/CPM.tex` - Coercive Projection Method framework

**Current State**: Skeleton complete with ~25 sorries organized by priority.

---

## The Proof Structure

```
                    ┌─────────────────────────────────┐
                    │     Goldbach Conjecture         │
                    │  ∀ n ≥ 4, even n = p + q       │
                    └─────────────┬───────────────────┘
                                  │
                    ┌─────────────▼───────────────────┐
                    │  uniformPointwisePositivity     │
                    │  (conditional on MED-L4)        │
                    └─────────────┬───────────────────┘
                                  │
              ┌───────────────────┼───────────────────┐
              │                   │                   │
    ┌─────────▼─────────┐ ┌──────▼──────┐ ┌─────────▼─────────┐
    │  coercivity_lemma │ │  MED-L4     │ │ ComputationalClosure│
    │  (arc splitting)  │ │  (THE KEY)  │ │ (finite verify)    │
    └─────────┬─────────┘ └──────┬──────┘ └───────────────────┘
              │                  │
    ┌─────────▼─────────┐ ┌──────▼──────────────────────┐
    │ major_arc_main_term│ │ mediumArcL4Saving_exists   │
    │ deep_minor_L2_bound│ │ bilinear_dispersion        │
    └─────────┬─────────┘ │ local_L4_short_arcs        │
              │           └──────┬──────────────────────┘
    ┌─────────▼─────────┐        │
    │ singularSeries_*  │        │
    │ χ₈_mul, K₈_*      │ ┌──────▼──────────────────────┐
    └───────────────────┘ │ Vaughan + Completion +      │
                          │ Large Sieve + Kloosterman   │
                          └─────────────────────────────┘
```

---

## Priority Queue (Work on these in order)

### P0: Critical Path (blocks everything)
1. **`mediumArcL4Saving_exists`** - THE bottleneck
2. **`bilinear_dispersion`** - Vaughan decomposition + dispersion

### P1: Core Infrastructure  
3. `χ₈_mul` - Character multiplicativity
4. `K₈_periodic`, `K₈_nonneg` - Kernel properties
5. `singularSeries_lower_bound` - Euler product

### P2: Arc Analysis
6. `major_arc_main_term` - Singular series on major arcs
7. `deep_minor_L2_bound` - Mean-square via Vaughan
8. `local_L4_short_arcs` - Elementary L⁴ lemma

### P3: Integration
9. `coercivity_lemma` - Combine arc bounds
10. `densityOnePositivity` - Average argument
11. `shortIntervalPositivity` - Chebyshev/Markov

### P4: Extensions
12. `chenSelbergVariant` - Prime + almost-prime
13. `uniformPointwisePositivity` - Final assembly

---

## Working Instructions

### Before Starting
```bash
cd /Users/jonathanwashburn/Projects/goldbach
lake build 2>&1 | head -50  # Check current state
```

### Workflow
1. **Read** the current sorry you're targeting
2. **Check** the LaTeX manuscript (`goldbach_rs.tex`) for mathematical details
3. **Search** `riemann_lean_repo/` for relevant Lean code to adapt
4. **Implement** the proof, using `sorry` for sub-lemmas if needed
5. **Test** with `lake build`
6. **Update** `.prompts/PROGRESS.md` with what you did

### Code Style
- Follow Mathlib conventions
- Use `sorry` for anything non-trivial you can't finish
- Add doc-strings explaining the mathematics
- Reference literature: `[Vaughan1997]`, `[MontgomeryVaughan2007]`, etc.

### When Stuck
- Check if similar results exist in `riemann_lean_repo/PrimeNumberTheoremAnd/`
- Search Mathlib for relevant lemmas
- Break the problem into smaller sorries and note dependencies

---

## Key Mathematical References

| Citation | Content | Use For |
|----------|---------|---------|
| [Vaughan1997] | Hardy-Littlewood method | Major arcs, Vaughan identity |
| [MontgomeryVaughan2007] | Multiplicative NT | Mean-square bounds, large sieve |
| [DeshouillersIwaniec1982] | Kloosterman sums | MED-L4 dispersion |
| [DukeFriedlanderIwaniec1997] | Bilinear Kloosterman | MED-L4 dispersion |
| [IwaniecKowalski2004] | Analytic NT | Everything, esp. Ch. 16 |

---

## Multi-Agent Tracks (Optional)

If running multiple agents, assign them to different tracks:

| Track | Focus | Files | Agent Prompt |
|-------|-------|-------|--------------|
| A | Foundations | `@.prompts/TRACK_A_FOUNDATIONS.md` | Kernel, characters |
| B | Arc Analysis | `@.prompts/TRACK_B_ARCS.md` | Major/minor bounds |
| C | Dispersion | `@.prompts/TRACK_C_DISPERSION.md` | THE KEY: MED-L4 |
| D | Assembly | `@.prompts/TRACK_D_ASSEMBLY.md` | Main theorems |

---

## Success Criteria

The project is **complete** when:
1. `lake build` produces no errors
2. All sorries are either filled OR explicitly marked as `axiom` with justification
3. The main theorem compiles:
   ```lean
   theorem goldbach_conditional : ∀ n, 4 ≤ n → n % 2 = 0 →
     ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ n = p + q
   ```

---

## Session Template

Start each session with:
```
I'm continuing work on the Goldbach formalization.

Current target: [sorry name from priority queue]
Last session: [brief summary or "fresh start"]

Let me check the current state and make progress.
```

