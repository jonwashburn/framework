import Mathlib
open scoped BigOperators

namespace Test

noncomputable def projectToNeutral (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  let mean := (Finset.univ.sum v) / 8
  fun i => v i - mean

lemma projectToNeutral_add (v δ : Fin 8 → ℂ) :
    projectToNeutral (fun i => v i + δ i) = fun i => projectToNeutral v i + projectToNeutral δ i := by
  classical
  unfold projectToNeutral
  ext i
  -- mean(v+δ) = mean(v) + mean(δ)
  simp [Finset.sum_add_distrib, add_div]
  ring

end Test
