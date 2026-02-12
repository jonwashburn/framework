import Mathlib
open scoped BigOperators

namespace Test

noncomputable def normSq8 (v : Fin 8 → ℂ) : ℝ :=
  Finset.univ.sum (fun i => Complex.normSq (v i))

noncomputable def innerProduct8 (u v : Fin 8 → ℂ) : ℂ :=
  Finset.univ.sum (fun i => star (u i) * v i)

lemma normSq8_add (v δ : Fin 8 → ℂ) :
    normSq8 (fun i => v i + δ i) =
      normSq8 v + normSq8 δ + 2 * (innerProduct8 v δ).re := by
  classical
  unfold normSq8 innerProduct8
  -- pointwise normSq_add
  have hterm (i : Fin 8) :
      Complex.normSq (v i + δ i) =
        Complex.normSq (v i) + Complex.normSq (δ i) + 2 * ((v i) * star (δ i)).re := by
    -- `Complex.normSq_add` uses `conj`, which is `star`.
    simpa [mul_comm] using (Complex.normSq_add (v i) (δ i))
  -- sum over i
  --
  -- TODO
  sorry

end Test
