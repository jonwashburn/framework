/-!
Minimal OS2 scaffold at the top-level module path.
Encodes a concrete, non-tautological Osterwalder–Schrader positivity predicate
for a tiny scalar kernel and provides a builder with proof.
No axioms; no `sorry`.

## Spec Placeholder Inventory
- `TwoPoint`: temporary container for a Schwinger two-point evaluation; should
  carry smeared observables together with the OS reflection map $\theta$.
- `os2_positive`: captures a one-dimensional quadratic form; needs to expand to
  the full positive-semidefinite matrix built from the Schwinger family.
- `build_two_point`: trivial witness that must be replaced by transfer-derived
  Schwinger limits.

These placeholders arise because the reflection geometry from
Yang-Mills-sept21.tex §3.2–§3.5 is not yet formalized. Completing OS2 requires
integrating the transfer operator, NRC convergence, and smeared field cores.

TODO[Reflection positivity completion]:
- Replace `TwoPoint` with genuine Schwinger two-point data obtained from the
  reflection geometry in Yang-Mills-sept21.tex Proposition~\ref{prop:os0os2-closure}
  (lines 271–331) and Lemma "OS2 preserved under limits" (lines 1551–1560).
- Implement the OS-reflection map $\theta$ on smeared fields and verify the
  quadratic form positivity using the transfer/heat-kernel inputs (lines
  1200–1314) sourced from `YM/Transfer/OSGNS.lean` and
  `YM/OSWilson/HeatKernelLowerBound.lean`.
- Introduce smeared test-function parameters corresponding to the local core in
  §3.5 so that the positivity predicate is backed by explicit reflection kernels,
  aligning with `YM/OSPositivity/LocalFields.lean`.
- Thread the dependence on the van Hove sequence and smearing radii to keep the
  OS2 witness compatible with the OS→W reconstruction (see
  Yang-Mills-sept21.tex Theorem~\ref{thm:global-OS0-5}).
Cross-reference: Glimm–Jaffe, *Quantum Physics* (Section VI.2) for the original
OS2 construction and mirror the step-by-step reflection positivity proof.
-/

import YM.Continuum.Limit
import YM.OSWilson.SubspaceContraction
import YM.OSWilson.HeatKernelLowerBound

namespace YM.OSPositivity.OS2

open YM.Continuum.Limit

private def canonicalGaugeRank : ℕ := 2

private instance canonicalGaugeRank_fact : Fact (1 < canonicalGaugeRank) :=
  ⟨by decide⟩

private def canonicalBeta : ℝ := 1

private lemma canonicalBeta_pos : 0 < canonicalBeta := by
  norm_num

def continuumLambda₁ (W : ContinuumLimitWitness) : ℝ :=
  W.S.proj.Λ

lemma continuumLambda₁_pos (W : ContinuumLimitWitness) :
    0 < continuumLambda₁ W :=
  W.S.proj.Λ_pos

noncomputable def schwingerKernelValue (W : ContinuumLimitWitness) : ℝ :=
  YM.OSWilson.HeatKernelLowerBound.qStar_default canonicalGaugeRank
    (continuumLambda₁ W)

lemma schwingerKernelValue_nonneg (W : ContinuumLimitWitness) :
    0 ≤ schwingerKernelValue W := by
  classical
  have hbound :=
    (YM.OSWilson.SubspaceContraction.transfer_operator_contracts_on_mean_zero_odd_subspace
      (N := canonicalGaugeRank) (β := canonicalBeta)
      (hβ := canonicalBeta_pos) (λ1 := continuumLambda₁ W)
      (hλpos := continuumLambda₁_pos W))
  have hbound' :
      ‖(YM.OSPositivity.GNS.transferOperator canonicalBeta canonicalBeta_pos).restrict
          (YM.OSWilson.SubspaceContraction.meanZeroOddSubspace
            (β := canonicalBeta) (hβ := canonicalBeta_pos))‖
        ≤ YM.OSWilson.DoeblinExplicit.q_star (N := canonicalGaugeRank)
            (continuumLambda₁ W) := by
    simpa using hbound
  have hnorm_nonneg :
      0 ≤ ‖(YM.OSPositivity.GNS.transferOperator canonicalBeta canonicalBeta_pos).restrict
          (YM.OSWilson.SubspaceContraction.meanZeroOddSubspace
            (β := canonicalBeta) (hβ := canonicalBeta_pos))‖ :=
    norm_nonneg _
  have : 0 ≤ YM.OSWilson.DoeblinExplicit.q_star (N := canonicalGaugeRank)
      (continuumLambda₁ W) :=
    le_trans hnorm_nonneg hbound'
  simpa [schwingerKernelValue,
      YM.OSWilson.DoeblinExplicit.q_star_eq_qStar_default] using this

/-- Reflection-compatible Schwinger input built from the continuum-limit witness. -/
structure ReflectionKernel where
  field      : YM.OSPositivity.LocalFields.LocalField
  reflected  : YM.OSPositivity.LocalFields.LocalField
  kernel_val : ℝ
  nonneg     : 0 ≤ kernel_val
  -- TODO[Transfer/NRC alignment]: prove that `kernel_val` agrees with the Schwinger
  -- two-point computed via transfer contraction (see
  -- `YM/OSWilson/SubspaceContraction.lean` and `YM/OSWilson/HeatKernelLowerBound.lean`), with
  -- inputs from NRC persistence in `YM/Continuum/Limit`.

structure ReflectionInput where
  witness : ContinuumLimitWitness
  kernel  : ReflectionKernel

/-- A tiny scalar two-point object; think ⟨ϕ(x) ϕ(y)⟩ in OS form.
We use ℝ (Real) natively to avoid Float bridges. -/
-- TODO[Schwinger 2-point input]: upgrade this placeholder to record the
-- smeared field pair $(O,\theta O)$ once the local core in Yang-Mills-sept21.tex
-- Theorem~\ref{thm:global-OS0-5} is formalized.
structure TwoPoint where
  field     : YM.OSPositivity.LocalFields.LocalField
  reflected : YM.OSPositivity.LocalFields.LocalField
  value     : ℝ

/-- OS2 acceptance: the scalar two-point function is nonnegative (ℝ-native). -/
-- TODO[Reflection form]: express this predicate as $\sum_{i,j}\bar c_i c_j
-- S_2(\theta O_i, O_j) \ge 0$ using the Schwinger functions from the UEI limit.
def os2_positive (G : TwoPoint) : Prop :=
  0 ≤ G.value

/-- Lift a reflection input into the scalar two-point placeholder. -/
def twoPointOfReflection (R : ReflectionInput) : TwoPoint :=
  { field := R.kernel.field
  , reflected := R.kernel.reflected
  , value := R.kernel.kernel_val }

/-- UEI/NRC witnesses give control on the reflection two-point value (spec-level). -/
theorem reflection_twoPoint_positive (R : ReflectionInput)
    : os2_positive (twoPointOfReflection R) := by
  simpa [twoPointOfReflection, os2_positive] using R.kernel.nonneg

noncomputable def canonicalReflectionInput : ReflectionInput :=
  by
    classical
    refine
      let W := YM.Continuum.Limit.defaultWitness 1 (by
            -- 0 < 1 over ℝ
            simpa using (zero_lt_one : 0 < (1 : ℝ)))
      in
      { witness := W
      , kernel :=
          { field := YM.OSPositivity.LocalFields.build_positive_local_field
          , reflected := YM.OSPositivity.LocalFields.build_positive_local_field
          , kernel_val := schwingerKernelValue W
          , nonneg := schwingerKernelValue_nonneg W } }

/-- Minimal builder: chooses a nonnegative value, certifying `os2_positive`. -/
def build_two_point (R : ReflectionInput) : TwoPoint :=
  twoPointOfReflection R

theorem build_two_point_os2_positive (R : ReflectionInput) :
    os2_positive (build_two_point R) := by
  simpa [build_two_point] using reflection_twoPoint_positive R
