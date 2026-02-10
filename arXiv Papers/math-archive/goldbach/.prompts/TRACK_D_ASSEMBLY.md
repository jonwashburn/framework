# Track D: Assembly (Main Theorems)

## Scope
Combine results from Tracks A, B, C into the final theorems.

## Prerequisites
- Track A: Kernel foundations (χ₈, K₈ properties)
- Track B: Arc bounds (major/minor)
- Track C: Dispersion (for conditional results)

## Your Sorries (in order)

### D1: `coercivity_lemma` - The key linking inequality
```lean
theorem coercivity_lemma (η : SmoothCutoff) (params : ArcParameters N)
    (m : ℕ) (hm : m ≤ N) (hN : (100 : ℕ) ≤ N) :
    R₈ η m N ≥ majorArcIntegral η params m -
      (1 / Real.sqrt 2) * Real.sqrt (mediumArcMeasure params) *
        Real.sqrt (mediumArcDefect η params) -
      εDeep η params 10
```

**Approach**:
1. Write R₈ as integral over [0,1)
2. Split [0,1) = M ∪ M_med ∪ m_deep
3. Major arcs: use `major_arc_main_term`
4. Medium arcs: Cauchy-Schwarz → √(measure) · √(defect)
5. Deep minor: triangle inequality → εDeep

### D2: `densityOnePositivity` - Almost all evens (UNCONDITIONAL)
```lean
theorem densityOnePositivity (η : SmoothCutoff) (params : ArcParameters N)
    (hN : (100 : ℕ) ≤ N) :
    ∃ (exceptional : Finset ℕ),
      (∀ m ∈ exceptional, m ≤ N) ∧
      exceptional.card ≤ N / (Real.log N) ^ 2 ∧
      ∀ m, m ≤ N → m ∉ exceptional → 0 < R₈ η m N
```

**Approach**:
1. Sum |minor arc contribution|² over m
2. By Parseval/Plancherel, this ≤ ∫|S|⁴ ≤ I_minor
3. Chebyshev: #{m : |minor| > T(N)} ≤ I_minor / T(N)²
4. Choose T(N) = (1/2) · main term → exceptional set is small

### D3: `shortIntervalPositivity` - Bounded gaps (UNCONDITIONAL)
```lean
theorem shortIntervalPositivity (η : SmoothCutoff) (params : ArcParameters N)
    (hN : (100 : ℕ) ≤ N) :
    ∃ (H₀ : ℝ), H₀ ≤ 500 * (Real.log N) ^ 8 ∧
      ∀ (M : ℕ), M + ⌈H₀⌉₊ ≤ N →
        ∃ m, M < m ∧ m ≤ M + ⌈H₀⌉₊ ∧ 0 < R₈ η m N
```

**Approach**:
1. In any interval of length H, count exceptions
2. #{exceptions in [M, M+H]} ≤ I_minor^{K8} / T(N)²
3. If H > I_minor^{K8} / T(N)², at least one m is good
4. With I_minor ≤ C·N²(log N)⁴ and T(N) ≈ N/(log N)², get H₀ ≈ (log N)⁸

### D4: `shortIntervalPositivity_improved` - Better gaps (CONDITIONAL)
```lean
theorem shortIntervalPositivity_improved (η : SmoothCutoff) (params : ArcParameters N)
    (hN : Real.exp 100 ≤ N) (saving : MediumArcL4Saving N) :
    ∃ (H₀ : ℝ), H₀ ≤ 500 * (Real.log N) ^ (8 - saving.δ_med) ∧ [...]
```

Same as D3 but using the L⁴ saving from Track C.

### D5: `uniformPointwisePositivity` - All large evens (CONDITIONAL)
```lean
theorem uniformPointwisePositivity (η : SmoothCutoff)
    (hSaving : ∀ N, Real.exp 100 ≤ N → ∃ s : MediumArcL4Saving N, s.C_disp ≤ 10^3) :
    ∃ (N₀ : ℕ), N₀ = Nat.ceil (Real.exp 75) ∧
      ∀ N m, N₀ ≤ N → m ≤ N → 0 < R₈ η m N
```

**Approach**:
1. Use coercivity: R₈ ≥ main - C·√(D_med) - ε_deep
2. With MED-L4 saving, √(D_med) ≤ C' · N · (log N)^{2 - δ/2}
3. For N ≥ N₀, the main term dominates: main > C·√(D_med) + ε_deep
4. Solve for N₀ explicitly

### D6: `chenSelbergVariant` - Prime + almost-prime (UNCONDITIONAL)
```lean
theorem chenSelbergVariant (η : SmoothCutoff) :
    ∃ (M₀ : ℕ), ∀ m, M₀ ≤ m →
      ∃ (p : ℕ) (q : ℕ), Nat.Prime p ∧ isP₂ q ∧ 2 * m = p + q
```

**Approach**: 
1. Replace Λ with Selberg lower-bound sieve weight W
2. Same major/minor arc analysis
3. W detects primes + almost-primes with positive density
4. Computable M₀ from sieve constants

### D7: `goldbach_conditional` - Final assembly
```lean
theorem goldbach_conditional
    (hSaving : [...]) (hComputed : ComputationalClosure (Nat.ceil (Real.exp 75))) :
    ∀ n, 4 ≤ n → n % 2 = 0 → ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ n = p + q
```

**Approach**:
1. For n ≤ 2·exp(75): use hComputed
2. For n > 2·exp(75): use uniformPointwisePositivity

## Completion Checklist
- [ ] D1: `coercivity_lemma`
- [ ] D2: `densityOnePositivity`
- [ ] D3: `shortIntervalPositivity`
- [ ] D4: `shortIntervalPositivity_improved` (needs Track C)
- [ ] D5: `uniformPointwisePositivity` (needs Track C)
- [ ] D6: `chenSelbergVariant`
- [ ] D7: `goldbach_conditional`

## Note on Dependencies

```
D1 (coercivity) ─────────────────┬─────────────────┐
                                 │                 │
D2 (density-one) ◄───────────────┤                 │
                                 │                 │
D3 (short-interval) ◄────────────┤                 │
                                 │                 │
D4 (improved) ◄──────────────────┼── Track C ◄────┤
                                 │                 │
D5 (uniform) ◄───────────────────┼── Track C ◄────┤
                                 │                 │
D6 (Chen) ◄──────────────────────┘                 │
                                                   │
D7 (final) ◄───────────────────── D5 + Compute ◄──┘
```

D2, D3, D6 can be completed without Track C.
D4, D5, D7 are conditional on Track C success.

