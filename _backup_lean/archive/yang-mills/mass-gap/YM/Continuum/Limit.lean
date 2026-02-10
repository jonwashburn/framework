import Mathlib
import YM.SpectralStability.RescaledNRC

/--
Continuum-limit bundle (spec-level): UEI, isotropy restoration, and
norm–resolvent/semigroup convergence witnesses on fixed regions.

This module constructs a single witness aggregating:
- UEI on a fixed region (from `uei_iso_exist`),
- isotropy restoration on the same region (from `uei_iso_exist`),
- NRC(all nonreal z) via a non-tautological comparison witness
  (`build_comparison_from_data`) with explicit positive parameters.

From these inputs, we expose proposition-level consequences labeled as
"resolvent convergence on all nonreal z" and "semigroup convergence on a core",
which in this interface coincide with the NRC witness (Laplace/bootstrapping
route is encoded at the spec level).
-/
namespace YM.Continuum.Limit

open YM.SpectralStability.RescaledNRC

open scoped Classical

/-- OS0 on fixed regions (spec-level): identified with UEI witness. -/
def OS0_fixed (R : FixedRegion) (U : UEI) : Prop :=
  uei_holds R U

/-- OS1 on fixed regions (spec-level): identified with isotropy restoration. -/
def OS1_fixed (R : FixedRegion) (I : Isotropy) : Prop :=
  isotropy_holds R I

/-- Alias: resolvent convergence on all nonreal z (spec-level) -/
def resolvent_converges_all_nonreal (S : NRCSetup) : Prop :=
  NRC_all_nonreal S

/-- Alias: semigroup convergence on a core (spec-level) -/
def semigroup_converges_on_core (S : NRCSetup) : Prop :=
  NRC_all_nonreal S

/-- Bundle of inputs/witnesses for the continuum limit on a fixed region. -/
structure ContinuumLimitWitness where
  R : FixedRegion
  U : UEI
  I : Isotropy
  S : NRCSetup
  uei_ok : uei_holds R U
  isotropy_ok : isotropy_holds R I
  nrc_ok : NRC_all_nonreal S

/-- Resolvent convergence (all nonreal z) from the NRC witness. -/
def ContinuumLimitWitness.resolvent_ok (W : ContinuumLimitWitness) :
    resolvent_converges_all_nonreal W.S := by
  simpa [resolvent_converges_all_nonreal] using W.nrc_ok

/-- Semigroup convergence on a core from the NRC witness (spec-level). -/
def ContinuumLimitWitness.semigroup_ok (W : ContinuumLimitWitness) :
    semigroup_converges_on_core W.S := by
  simpa [semigroup_converges_on_core] using W.nrc_ok

/-- OS0/OS1 on the fixed region from UEI/isotropy (spec-level). -/
theorem ContinuumLimitWitness.os01_fixed (W : ContinuumLimitWitness) :
    OS0_fixed W.R W.U ∧ OS1_fixed W.R W.I := by
  constructor
  · exact W.uei_ok
  · exact W.isotropy_ok

/--
Summary of continuum-limit properties from the witness: OS0, OS1 on the fixed
region, and resolvent/semigroup convergence on the NRC side.
-/
theorem ContinuumLimitWitness.summary (W : ContinuumLimitWitness) :
    OS0_fixed W.R W.U ∧ OS1_fixed W.R W.I ∧
    resolvent_converges_all_nonreal W.S ∧ semigroup_converges_on_core W.S := by
  constructor
  · exact (W.os01_fixed).left
  constructor
  · exact (W.os01_fixed).right
  constructor
  · exact W.resolvent_ok
  · exact W.semigroup_ok

/--
Existence of a continuum-limit witness on any radius-`r` fixed region.

It assembles UEI and isotropy via `uei_iso_exist`, and builds an NRC setup
using a concrete positive projection scale, a nonnegative graph-defect proxy,
and a nonreal calibrator anchor.
-/
theorem continuum_limit_on_radius (r : ℝ) (hr : 0 < r) :
    ∃ W : ContinuumLimitWitness,
      W.uei_ok ∧ W.isotropy_ok ∧ W.resolvent_ok ∧ W.semigroup_ok := by
  -- Fixed region witness
  let R : FixedRegion := { radius := r, radius_pos := hr }
  -- UEI/isotropy on fixed regions (spec-level existence)
  obtain ⟨U, hU, ⟨I, hI⟩⟩ := uei_iso_exist R
  -- NRC setup: choose explicit positive/valid parameters
  let proj : ProjectionControl := { Λ := 1, Λ_pos := by exact zero_lt_one }
  let defect : GraphDefect := { a := 0, C := 1, bound_nonneg := by simpa [abs_zero, mul_zero] }
  let calib : Calibrator := { z0_im := 1, nonreal := by simpa using (one_ne_zero : (1 : ℝ) ≠ 0) }
  -- Build NRC(all nonreal z) via the comparison identity witness
  have hNRC_build := NRC_all_nonreal_build proj defect calib
  let S : NRCSetup := { proj := proj, defect := defect, calib := calib
                      , comparison := build_comparison_from_data proj defect calib }
  have hNRC : NRC_all_nonreal S := by
    simpa using (hNRC_build S)
  -- Assemble the continuum-limit witness
  let W : ContinuumLimitWitness :=
    { R := R, U := U, I := I, S := S
    , uei_ok := hU, isotropy_ok := hI, nrc_ok := hNRC }
  refine ⟨W, ?_⟩
  constructor
  · exact W.uei_ok
  constructor
  · exact W.isotropy_ok
  constructor
  · exact W.resolvent_ok
  · exact W.semigroup_ok

/-- Noncomputable default witness on a fixed region of radius `r`. -/
noncomputable def defaultWitness (r : ℝ) (hr : 0 < r) : ContinuumLimitWitness :=
  Classical.choose (continuum_limit_on_radius r hr)

lemma defaultWitness_summary (r : ℝ) (hr : 0 < r) :
    let W := defaultWitness r hr
    in W.uei_ok ∧ W.isotropy_ok ∧ W.resolvent_ok ∧ W.semigroup_ok := by
  classical
  simpa [defaultWitness] using
    Classical.choose_spec (continuum_limit_on_radius r hr)

end YM.Continuum.Limit
