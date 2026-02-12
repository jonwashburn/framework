import Mathlib
import YM.Continuum.Limit

/--
Global continuum bundle: for every radius `r>0`, supplies a fixed-region
continuum witness and exports OS0/OS1 on the region and resolvent/semigroup
convergence (spec-level).
-/
namespace YM.Continuum.Global

open YM.Continuum.Limit

noncomputable section

structure GlobalContinuum where
  witness : ∀ r : ℝ, 0 < r → ContinuumLimitWitness
  os0 : ∀ r hr, OS0_fixed (witness r hr).R (witness r hr).U
  os1 : ∀ r hr, OS1_fixed (witness r hr).R (witness r hr).I
  resolvent : ∀ r hr, resolvent_converges_all_nonreal (witness r hr).S
  semigroup : ∀ r hr, semigroup_converges_on_core (witness r hr).S

/-- Build a global continuum bundle by choosing a fixed-region witness for each
radius `r>0` using `continuum_limit_on_radius`. -/
def build : GlobalContinuum := by
  classical
  refine {
    witness := ?w
  , os0 := ?o0
  , os1 := ?o1
  , resolvent := ?or
  , semigroup := ?sg };
  · intro r hr
    exact Classical.choose (continuum_limit_on_radius r hr)
  · intro r hr
    let W := Classical.choose (continuum_limit_on_radius r hr)
    have h := Classical.choose_spec (continuum_limit_on_radius r hr)
    -- h: W.uei_ok ∧ W.isotropy_ok ∧ W.resolvent_ok ∧ W.semigroup_ok
    simpa [OS0_fixed] using h.left
  · intro r hr
    let W := Classical.choose (continuum_limit_on_radius r hr)
    have h := Classical.choose_spec (continuum_limit_on_radius r hr)
    -- isotropy on the fixed region
    simpa [OS1_fixed] using h.right.left
  · intro r hr
    let W := Classical.choose (continuum_limit_on_radius r hr)
    have h := Classical.choose_spec (continuum_limit_on_radius r hr)
    -- resolvent convergence on all nonreal z
    simpa [resolvent_converges_all_nonreal] using h.right.right.left
  · intro r hr
    let W := Classical.choose (continuum_limit_on_radius r hr)
    have h := Classical.choose_spec (continuum_limit_on_radius r hr)
    -- semigroup convergence on a core
    simpa [semigroup_converges_on_core] using h.right.right.right

/-- Existence of a global continuum bundle (spec-level). -/
theorem exists_global : ∃ G : GlobalContinuum, True :=
  ⟨build, trivial⟩

end


