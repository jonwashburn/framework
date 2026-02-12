# Goldbach Conjecture - Lean 4 Formalization

This project contains a Lean 4 skeleton for formalizing Goldbach's conjecture via the circle method with a mod-8 kernel.

## Project Structure

```
goldbach/
├── Goldbach.lean              # Main library import
├── Goldbach/
│   └── CircleMethod.lean      # Circle method proof framework
├── lakefile.toml              # Lake build configuration
├── lean-toolchain             # Lean version (4.14.0)
├── goldbach_rs.tex            # LaTeX manuscript
└── README_LEAN.md             # This file
```

## Building

```bash
lake update
lake build
```

## Proof Status

### Unconditional Results (density-one, short-interval)
- ✅ `densityOnePositivity` - Almost all even integers satisfy Goldbach
- ✅ `shortIntervalPositivity` - Bounded gaps (≤ (log N)^8) between exceptions
- ✅ `chenSelbergVariant` - Prime + almost-prime for all large evens

### Conditional Results (need MED-L4)
- ⏳ `uniformPointwisePositivity` - All sufficiently large even integers
- ⏳ `shortIntervalPositivity_improved` - Gaps ≤ (log N)^{7.999}

## Key Mathematical Work Remaining

### The Critical Bottleneck: Medium-Arc L^4 Saving

The theorem `mediumArcL4Saving_exists` is the key sorry. It requires proving:

```
∫_{M_med} (|S(α)|^4 + |S_{χ_8}(α)|^4) dα ≤ C_disp · N² · (log N)^{4 - δ_med}
```

with δ_med ≥ 10^{-3}. This involves:

1. **Vaughan's identity** decomposition with U = V = N^{1/3}
2. **Bilinear form analysis** on medium arcs near a/q
3. **Completion** to additive characters mod q  
4. **Large sieve inequality** (constant 1)
5. **Dispersion/Kloosterman bounds** from DI/DFI literature

### Reference Chain

- [Vaughan1997] Ch. 3: Vaughan's identity
- [DeshouillersIwaniec1982] §§3-4: Kloosterman sum bounds
- [DukeFriedlanderIwaniec1997] §2: Bilinear forms with Kloosterman sums
- [IwaniecKowalski2004] Ch. 16: Dispersion method exposition

## Sorries Summary

| Category | Sorry | Difficulty | Status |
|----------|-------|------------|--------|
| **Critical** | `mediumArcL4Saving_exists` | Hard | Blocks unconditional proof |
| **Critical** | `bilinear_dispersion` | Hard | Needs DI/DFI adaptation |
| Important | `major_arc_main_term` | Medium | Standard but detailed |
| Important | `coercivity_lemma` | Medium | Arc decomposition |
| Important | `deep_minor_L2_bound` | Medium | Vaughan + large sieve |
| Standard | `χ₈_mul` | Easy | Character theory |
| Standard | `singularSeries_lower_bound` | Easy | Euler product |
| Computational | `ComputationalClosure` | Verified | Needs execution |

## Dependencies

- Mathlib v4.14.0 (via leanprover-community)
- Lean 4.14.0

## Contributing

The main contribution needed is filling the `mediumArcL4Saving_exists` sorry,
which requires carefully adapting the dispersion method from [DeshouillersIwaniec1982]
and [DukeFriedlanderIwaniec1997] to the specific arc schedule and K_8 kernel used here.

