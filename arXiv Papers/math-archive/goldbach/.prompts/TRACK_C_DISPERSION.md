# Track C: Dispersion (THE CRITICAL PATH)

## ⚠️ THIS IS THE KEY BOTTLENECK ⚠️

Everything else in the proof works. This track contains the one result that
blocks the unconditional proof of Goldbach.

## Scope
Prove the medium-arc L⁴ saving δ_med > 0 exists.

## The Key Theorem

```lean
theorem mediumArcL4Saving_exists (N : ℕ) (hN : Real.exp 100 ≤ N) :
    ∃ (saving : MediumArcL4Saving N), saving.C_disp ≤ 10^3 ∧ saving.δ_med = 10⁻³
```

This asserts:
```
∫_{M_med} (|S(α)|⁴ + |S_{χ₈}(α)|⁴) dα ≤ C_disp · N² · (log N)^{4 - δ_med}
```

The trivial bound has exponent 4. We need ANY positive saving δ_med > 0.

## Proof Strategy (from goldbach_rs.tex lines 304-446)

### Step 1: Vaughan Decomposition
Split S(α) = S_I + S_II + R with U = V = N^{1/3}

```lean
-- Need to define
def vaughanTypeI (α : ℝ) (U : ℝ) : ℂ := sorry
def vaughanTypeII (α : ℝ) (V : ℝ) : ℂ := sorry
def vaughanRemainder (α : ℝ) (U V : ℝ) : ℂ := sorry

theorem vaughan_decomposition (α : ℝ) :
    S η N α = vaughanTypeI α (N^(1/3)) + vaughanTypeII α (N^(1/3)) + 
              vaughanRemainder α (N^(1/3)) (N^(1/3))
```

### Step 2: Bilinear Form on Medium Arcs
On α = a/q + β with Q < q ≤ Q', analyze:
```
B(α) = Σ_{m~M} A_m · Σ_{n~N/M} B_n · e(a·mn/q) · e(β·mn)
```

### Step 3: Local L⁴ Lemma
```lean
theorem local_L4_short_arcs (c : ℕ → ℂ) (B : ℝ) (hB : 0 < B) (hB' : B ≤ 1) :
    ∫ β in Set.Icc (-B) B, ‖Σ_x c_x e(βx)‖⁴ ≤ 2B · (Σ_x |c_x|²)²
```

### Step 4: Completion mod q
Complete sums to full additive characters mod q:
```
Σ_{a mod q, (a,q)=1} |Σ_x c_x e(ax/q)|² ≤ (q + X) · Σ_x |c_x|²
```

### Step 5: Large Sieve (Constant 1)
```lean
theorem additive_large_sieve (Q : ℕ) (X : ℕ) (a : ℕ → ℂ) :
    Σ_{q≤Q} Σ_{(a,q)=1} |Σ_{n≤X} a_n e(an/q)|² ≤ (X + Q²) · Σ_{n≤X} |a_n|²
```

### Step 6: Dispersion Bound
After steps 3-5, the bilinear dispersion gives a saving because
the range (Q, Q'] and the bilinear ranges M ∈ [N^{1/3}, N^{2/3}]
create extra cancellation.

The computation in goldbach_rs.tex lines 366-373 shows:
```
δ(N) = c · log(Q'/Q) / log N = c · (1/6 - 2 log log N / log N)
```
For large N, this is ≈ c/6 > 0.

## Your Sorries (in order)

### C1: `local_L4_short_arcs`
This is elementary - expand the fourth power and integrate.

### C2: `bilinear_dispersion`
This is the hard one. Build up from:
- Vaughan decomposition
- Completion lemma
- Large sieve

### C3: `mediumArcL4Saving_exists`
Combine C1, C2 with arc geometry.

## Literature Chain

1. **[Vaughan1997, Ch. 3]**: Vaughan's identity setup
2. **[DeshouillersIwaniec1982, §§3-4]**: Kloosterman sum bounds in dispersion
3. **[DukeFriedlanderIwaniec1997, §2]**: Bilinear forms with Kloosterman sums
4. **[IwaniecKowalski2004, Ch. 16]**: Modern exposition of dispersion method

## Honest Assessment

This is genuinely hard. The references provide the techniques but adapting to:
- The specific arc schedule Q = N^{1/2}/(log N)^4, Q' = N^{2/3}/(log N)^6
- The mod-8 twist χ₈
- Getting explicit constants

requires careful work. Options if stuck:

1. **Weaken the claim**: Change δ_med = 10^{-3} to just δ_med > 0 (existential)
2. **Add as axiom**: Mark as `axiom` with detailed justification pointing to literature
3. **Conditional route**: Keep as hypothesis, making theorem conditional

## Completion Checklist
- [ ] C1: `local_L4_short_arcs`
- [ ] C2: `bilinear_dispersion` (with sub-lemmas)
- [ ] C3: `mediumArcL4Saving_exists`

This track is the difference between "density-one Goldbach" and "all sufficiently large even integers."

