Subject: Contribution: Original Hadamard Factorization & Analytic Bounds (Pre-Oct 2025)

Dear Professor Kontorovich,

I saw the recent Zulip discussion regarding Hadamard factorization contributions to PNT+. I am writing to offer the original, pre-formalized Lean modules for this topic directly to your repository.

These modules were authored by me in October 2025 as part of my independent research on the Riemann Hypothesis. While you may have seen recent "refactored" submissions to Mathlib under my name (performed by a contractor), the code I am offering here is the original, verified source from before that contractor was hired.

### What this bundle provides
It directly fills the gap in `HadamardFactorization.lean` and supports the explicit estimates track:

1.  **`WeierstrassProduct.lean`**:
    *   Defines Weierstrass elementary factors $E_m(z)$ (genus 1).
    *   Proves the key cubic tail bound $\|\log(1-z) + z + z^2/2\| \le |z|^3/(1-|z|)$.
    *   Bridges summable logs to infinite products.

2.  **`Determinant.lean`**:
    *   Defines the 2-modified Fredholm determinant $\det_2(I-A)$ as an Euler product.
    *   **Crucially:** Proves non-vanishing on $\Re(s) > 1/2$. This is the core analytic step for the Hadamard factorization of $\xi(s)$.

3.  **`GammaBounds.lean`**:
    *   Provides uniform bounds for the Archimedean factor $\Gamma(s/2)\pi^{-s/2}$ on vertical strips.

### Provenance & Integration
This code is fully self-contained (using a local `Common.lean` shim) and builds with your current Mathlib version. It resides in a clean repository here:

**[https://github.com/jonwashburn/PNT](https://github.com/jonwashburn/PNT)**

You can add this as a dependency or simply copy the files into `PrimeNumberTheoremAnd/`.

I understand you mentioned "we no longer 'need' Hadamard" due to Borel-Carathéodory, but since `HoffsteinLockhart.lean` still references it and Terence Tao expressed interest in it for the explicit PNT project, I hope this original, clean implementation will be useful to the community.

Best regards,

Jonathan Washburn
washburn.jonathan@gmail.com
