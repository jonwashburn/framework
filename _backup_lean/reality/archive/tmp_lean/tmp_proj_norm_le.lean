import Mathlib
open scoped BigOperators

namespace Test

noncomputable def projectToNeutral (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  let mean := (Finset.univ.sum v) / 8
  fun i => v i - mean

noncomputable def normSq8 (v : Fin 8 → ℂ) : ℝ :=
  Finset.univ.sum (fun i => Complex.normSq (v i))

lemma normSq8_nonneg (v : Fin 8 → ℂ) : 0 ≤ normSq8 v := by
  unfold normSq8
  refine Finset.sum_nonneg ?_
  intro i hi
  exact Complex.normSq_nonneg (v i)

lemma normSq8_projectToNeutral_le (v : Fin 8 → ℂ) :
    normSq8 (projectToNeutral v) ≤ normSq8 v := by
  classical
  unfold projectToNeutral
  set m : ℂ := (Finset.univ.sum v) / 8
  unfold normSq8
  -- rewrite each term using normSq_sub
  have hterm (i : Fin 8) :
      Complex.normSq (v i - m) =
        Complex.normSq (v i) + Complex.normSq m - 2 * ((v i) * star m).re := by
    -- `Complex.normSq_sub` uses `conj` via `starRingEnd`, so we normalize to `star`.
    --
    -- normSq(z - w) = normSq z + normSq w - 2*(z*star w).re
    simpa using (Complex.normSq_sub (v i) m)
  -- Sum both sides.
  --
  -- TODO
  sorry

end Test
