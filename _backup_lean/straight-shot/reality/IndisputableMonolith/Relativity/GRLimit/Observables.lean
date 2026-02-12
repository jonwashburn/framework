import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Observable Limits

Proves that basic proxy observables (w, γ, β, c_T²) reduce to GR values as parameters → 0,
using only continuity arguments within mathlib.
-/

namespace IndisputableMonolith
namespace Relativity
namespace GRLimit

open Filter Topology

noncomputable section

/-- Weight function w in a weak-field proxy model.
We use an exponential representation to avoid rpow domain issues. -/
def weight_observable (α cLag : ℝ) (Tdyn tau0 : ℝ) : ℝ :=
  let A : ℝ := Tdyn / tau0
  1 + (α * cLag) * Real.exp (α * Real.log A)

/-- Weight approaches 1 as (α,cLag) → (0,0), for any positive Tdyn,tau0. -/
 theorem weight_gr_limit (Tdyn tau0 : ℝ) (_h_Tdyn : 0 < Tdyn) (_h_tau0 : 0 < tau0) :
  Tendsto (fun params : ℝ × ℝ => weight_observable params.1 params.2 Tdyn tau0)
    (nhds (0, 0)) (nhds 1) := by
  have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
    continuous_fst.mul continuous_snd
  have A : ℝ := Tdyn / tau0
  have h_cont_g : Continuous fun p : ℝ × ℝ => Real.exp (p.1 * Real.log A) := by
    have : Continuous fun p : ℝ × ℝ => p.1 * Real.log A :=
      (continuous_fst.mul continuous_const)
    exact Real.continuous_exp.comp this
  have h_cont_weight : Continuous
      (fun p : ℝ × ℝ => 1 + (p.1 * p.2) * Real.exp (p.1 * Real.log A)) := by
    refine continuous_const.add ?_
    exact h_cont_mul.mul h_cont_g
  have h_tendsto := (h_cont_weight.tendsto (0, 0))
  have h_eval : (fun p : ℝ × ℝ => 1 + (p.1 * p.2) * Real.exp (p.1 * Real.log A)) (0, 0) = 1 := by
    simp
  simpa [weight_observable, h_eval] using h_tendsto

/-- PPN parameter γ proxy: γ = 1 + 0.1 · |α·cLag|. -/
 def gamma_observable (α cLag : ℝ) : ℝ := 1 + (0.1 : ℝ) * |α * cLag|

 theorem gamma_gr_limit :
  Tendsto (fun params : ℝ × ℝ => gamma_observable params.1 params.2)
    (nhds (0, 0)) (nhds 1) := by
  have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
    continuous_fst.mul continuous_snd
  have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
    continuous_abs.comp h_cont_mul
  have h_cont : Continuous fun p : ℝ × ℝ => 1 + (0.1 : ℝ) * |p.1 * p.2| := by
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h := h_cont.tendsto (0, 0)
  have : (fun p : ℝ × ℝ => 1 + (0.1 : ℝ) * |p.1 * p.2|) (0, 0) = 1 := by simp
  simpa [gamma_observable, this]

/-- PPN parameter β proxy: β = 1 + 0.05 · |α·cLag|. -/
 def beta_observable (α cLag : ℝ) : ℝ := 1 + (0.05 : ℝ) * |α * cLag|

 theorem beta_gr_limit :
  Tendsto (fun params : ℝ × ℝ => beta_observable params.1 params.2)
    (nhds (0, 0)) (nhds 1) := by
  have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
    continuous_fst.mul continuous_snd
  have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
    continuous_abs.comp h_cont_mul
  have h_cont : Continuous fun p : ℝ × ℝ => 1 + (0.05 : ℝ) * |p.1 * p.2| := by
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h := h_cont.tendsto (0, 0)
  have : (fun p : ℝ × ℝ => 1 + (0.05 : ℝ) * |p.1 * p.2|) (0, 0) = 1 := by simp
  simpa [beta_observable, this]

/-- GW tensor speed proxy: c_T² = 1 + 0.01 · |α·cLag|. -/
 def c_T_squared_observable (α cLag : ℝ) : ℝ := 1 + (0.01 : ℝ) * |α * cLag|

 theorem c_T_squared_gr_limit :
  Tendsto (fun params : ℝ × ℝ => c_T_squared_observable params.1 params.2)
    (nhds (0, 0)) (nhds 1) := by
  have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
    continuous_fst.mul continuous_snd
  have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
    continuous_abs.comp h_cont_mul
  have h_cont : Continuous fun p : ℝ × ℝ => 1 + (0.01 : ℝ) * |p.1 * p.2| := by
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h := h_cont.tendsto (0, 0)
  have : (fun p : ℝ × ℝ => 1 + (0.01 : ℝ) * |p.1 * p.2|) (0, 0) = 1 := by simp
  simpa [c_T_squared_observable, this]

/-- All four proxies approach GR values simultaneously. -/
 theorem observables_bundle_gr_limit (Tdyn tau0 : ℝ) (hT : 0 < Tdyn) (hτ : 0 < tau0) :
  Tendsto
    (fun params : ℝ × ℝ =>
      ( weight_observable params.1 params.2 Tdyn tau0
      , gamma_observable params.1 params.2
      , beta_observable params.1 params.2
      , c_T_squared_observable params.1 params.2 ))
    (nhds (0, 0)) (nhds (1, 1, 1, 1)) := by
  have h_w_cont : Continuous fun p : ℝ × ℝ => weight_observable p.1 p.2 Tdyn tau0 := by
    have A : ℝ := Tdyn / tau0
    have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
      continuous_fst.mul continuous_snd
    have h_cont_g : Continuous fun p : ℝ × ℝ => Real.exp (p.1 * Real.log A) := by
      have : Continuous fun p : ℝ × ℝ => p.1 * Real.log A :=
        (continuous_fst.mul continuous_const)
      exact Real.continuous_exp.comp this
    refine continuous_const.add ?_
    exact h_cont_mul.mul h_cont_g
  have h_g_cont : Continuous fun p : ℝ × ℝ => gamma_observable p.1 p.2 := by
    have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
      continuous_fst.mul continuous_snd
    have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
      continuous_abs.comp h_cont_mul
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h_b_cont : Continuous fun p : ℝ × ℝ => beta_observable p.1 p.2 := by
    have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
      continuous_fst.mul continuous_snd
    have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
      continuous_abs.comp h_cont_mul
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h_c_cont : Continuous fun p : ℝ × ℝ => c_T_squared_observable p.1 p.2 := by
    have h_cont_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
      continuous_fst.mul continuous_snd
    have h_cont_abs : Continuous fun p : ℝ × ℝ => |p.1 * p.2| :=
      continuous_abs.comp h_cont_mul
    refine continuous_const.add ?_
    exact continuous_const.mul h_cont_abs
  have h_tuple_cont : Continuous
      (fun p : ℝ × ℝ =>
        ( weight_observable p.1 p.2 Tdyn tau0
        , gamma_observable p.1 p.2
        , beta_observable p.1 p.2
        , c_T_squared_observable p.1 p.2 )) := by
    simpa using
      (((h_w_cont.prod_mk h_g_cont).prod_mk h_b_cont).prod_mk h_c_cont)
  have h := h_tuple_cont.tendsto (0, 0)
  have :
      (fun p : ℝ × ℝ =>
        ( weight_observable p.1 p.2 Tdyn tau0
        , gamma_observable p.1 p.2
        , beta_observable p.1 p.2
        , c_T_squared_observable p.1 p.2 )) (0, 0) = (1, 1, 1, 1) := by
    simp [weight_observable]
  simpa [this] using h

end

end GRLimit
end Relativity
end IndisputableMonolith
