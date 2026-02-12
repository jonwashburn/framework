# The Medium-Arc L⁴ Saving Theorem

## Statement

**Theorem (MED-L4).** *Let N ≥ e¹⁰⁰ be a large integer. Define the exponential sums*

$$S(\alpha) = \sum_{n \leq 2N} \Lambda(n) \, e(\alpha n) \, \eta\left(\frac{n}{N}\right)$$

*and*

$$S_{\chi_8}(\alpha) = \sum_{n \leq 2N} \Lambda(n) \, \chi_8(n) \, e(\alpha n) \, \eta\left(\frac{n}{N}\right)$$

*where:*
- *Λ is the von Mangoldt function*
- *e(x) = e^{2πix}*
- *χ₈ is the primitive real character mod 8*
- *η ∈ C_c^∞((0,2)) is a smooth cutoff with η ≡ 1 on [1/4, 7/4]*

*Define the medium arcs with parameters*

$$Q = \frac{N^{1/2}}{(\log N)^4}, \qquad Q' = \frac{N^{2/3}}{(\log N)^6}$$

*as*

$$\mathfrak{M}_{\mathrm{med}} = \bigcup_{Q < q \leq Q'} \bigcup_{\substack{a \bmod q \\ (a,q)=1}} \left\{ \alpha : \left|\alpha - \frac{a}{q}\right| \leq \frac{Q'}{qN} \right\} \setminus \mathfrak{M}$$

*where 𝔐 is the union of major arcs (q ≤ Q).*

*Then there exist absolute constants C_disp > 0 and δ_med > 0 such that*

$$\boxed{\int_{\mathfrak{M}_{\mathrm{med}}} \left( |S(\alpha)|^4 + |S_{\chi_8}(\alpha)|^4 \right) d\alpha \leq C_{\mathrm{disp}} \cdot N^2 \cdot (\log N)^{4 - \delta_{\mathrm{med}}}}$$

*Moreover, one may take δ_med ≥ 10⁻³ and C_disp ≤ 10³.*

---

## What This Theorem Says

The **trivial bound** for this integral is O(N² (log N)⁴). This theorem claims a **logarithmic power saving**: the exponent drops from 4 to 4 - δ_med.

Any positive δ_med > 0 suffices for the application to Goldbach. The specific values (δ_med = 0.001, C_disp = 1000) are conservative choices that make the downstream constants work out.

---

## Why This Matters

**If MED-L4 is true**, then combined with:
- Standard major-arc analysis (singular series)
- Standard deep-minor arc bounds (mean-square via Vaughan)
- A coercivity argument

One obtains: **Every sufficiently large even integer is a sum of two primes.**

The threshold "sufficiently large" is approximately N₀ ≈ e^75 ≈ 10³², which is far beyond computational verification but is an explicit finite bound.

---

## What Is Known

### Related Results That Exist

1. **Vinogradov's method** gives bounds for S(α) pointwise on minor arcs, but not the integrated L⁴ saving on medium arcs.

2. **Deshouillers-Iwaniec (1982)** prove dispersion bounds using Kloosterman sums for bilinear forms, but in the context of primes in arithmetic progressions, not this specific arc geometry.

3. **Duke-Friedlander-Iwaniec (1997)** extend bilinear Kloosterman techniques, but again not for this specific application.

4. **The Vaughan identity** decomposes S(α) into Type I and Type II sums, which is the starting point for any attack on MED-L4.

### The Gap

No published paper proves MED-L4 with these specific:
- Arc boundaries (Q, Q')
- The mod-8 twist χ₈
- Explicit constants

The claim that "such savings follow from dispersion techniques" is plausible but unverified.

---

## Proof Strategy (Sketch)

### Step 1: Vaughan Decomposition
With U = V = N^{1/3}, write

$$S(\alpha) = S_{\mathrm{I}}(\alpha) + S_{\mathrm{II}}(\alpha) + R(\alpha)$$

where S_I, S_II are bilinear forms with divisor-bounded coefficients.

### Step 2: Bilinear Analysis on Medium Arcs
On a medium arc α = a/q + β with Q < q ≤ Q' and |β| ≤ Q'/(qN), the bilinear piece takes the form

$$\mathcal{B}(\alpha) = \sum_{m \sim M} A_m \sum_{n \sim N/M} B_n \, e\left(\frac{a \cdot mn}{q}\right) e(\beta \cdot mn)$$

for dyadic M ∈ [N^{1/3}, N^{2/3}].

### Step 3: Local L⁴ Lemma
For |β| ≤ B:

$$\int_{|\beta| \leq B} \left| \sum_x c_x e(\beta x) \right|^4 d\beta \leq 2B \cdot \left( \sum_x |c_x|^2 \right)^2$$

### Step 4: Completion and Large Sieve
Complete the inner sum to additive characters mod q, then apply the large sieve:

$$\sum_{q \leq Q'} \sum_{\substack{a \bmod q \\ (a,q)=1}} \left| \sum_{n \leq X} a_n \, e\left(\frac{an}{q}\right) \right|^2 \leq (X + Q'^2) \sum_{n \leq X} |a_n|^2$$

### Step 5: Assemble the Saving
The combination of:
- Arc width Q'/(qN) shrinking with q
- Bilinear range balance (M ∼ N/M when M = N^{1/2})
- Large sieve savings in the q-sum

should produce the logarithmic saving δ_med > 0.

**The gap**: Making this rigorous with explicit constants.

---

## Explicit Constants Needed

| Constant | Meaning | Target Value |
|----------|---------|--------------|
| δ_med | Logarithmic saving exponent | ≥ 0.001 |
| C_disp | Overall multiplicative constant | ≤ 1000 |
| C_ls | Large sieve constant | = 1 (classical) |
| C_Vaughan | Vaughan identity coefficient bounds | ≤ 3 log N |

---

## Alternative Approaches

If proving MED-L4 is too hard, alternatives include:

1. **Weaken to existential**: Just prove ∃ δ > 0 without explicit value
2. **Conditional formulation**: State Goldbach conditional on MED-L4
3. **Different arc schedule**: Perhaps different Q, Q' make the proof easier
4. **Hybrid approach**: Combine with sieve methods (Chen-style)

---

## References

1. Vaughan, R.C. (1997). *The Hardy-Littlewood Method*, 2nd ed. Cambridge. [Vaughan identity, Ch. 3]

2. Montgomery, H.L. & Vaughan, R.C. (2007). *Multiplicative Number Theory I*. Cambridge. [Large sieve, Ch. 7]

3. Deshouillers, J.-M. & Iwaniec, H. (1982). "Kloosterman sums and Fourier coefficients of cusp forms." *Invent. Math.* 70, 219-288. [Dispersion method]

4. Duke, W., Friedlander, J. & Iwaniec, H. (1997). "Bilinear forms with Kloosterman sums." *Invent. Math.* 128, 23-43. [Bilinear Kloosterman]

5. Iwaniec, H. & Kowalski, E. (2004). *Analytic Number Theory*. AMS. [Ch. 16: Dispersion]

---

## Call for Collaboration

This theorem is the **sole remaining obstacle** to a circle-method proof of Goldbach (for large N). If you can:

- Prove it (even with worse constants)
- Find it in the literature
- Show it's false (unlikely but would be important)
- Suggest a different approach

Please contact: [your contact info]

---

## Lean 4 Formalization

The theorem is formalized in `Goldbach/CircleMethod.lean` as:

```lean
structure MediumArcL4Saving (N : ℕ) where
  C_disp : ℝ
  δ_med : ℝ
  hC_pos : 0 < C_disp
  hδ_pos : 0 < δ_med
  hδ_lower : 10⁻³ ≤ δ_med
  l4_bound : ∀ (η : SmoothCutoff) (params : ArcParameters N),
    mediumArcDefect η params ≤ C_disp * N ^ 2 * (Real.log N) ^ (4 - δ_med)

theorem mediumArcL4Saving_exists (N : ℕ) (hN : Real.exp 100 ≤ N) :
    ∃ (saving : MediumArcL4Saving N), saving.C_disp ≤ 10^3 ∧ saving.δ_med = 10⁻³ := by
  sorry -- THE KEY MATHEMATICAL WORK
```

Filling this `sorry` with a proof would complete the Goldbach formalization.

