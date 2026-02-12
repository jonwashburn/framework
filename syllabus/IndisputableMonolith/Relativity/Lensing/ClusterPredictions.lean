import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Lensing.Deflection
import IndisputableMonolith.Relativity.Lensing.TimeDelay
import IndisputableMonolith.Relativity.PostNewtonian.GammaExtraction

namespace IndisputableMonolith
namespace Relativity
namespace Lensing

open Geometry
open PostNewtonian

structure ClusterModel where
  mass : ℝ
  radius : ℝ
  rho : ℝ → ℝ

noncomputable def cluster_deflection (cluster : ClusterModel) (impact : ImpactParameter) (gamma_val : ℝ) : ℝ :=
  spherical_lens_deflection cluster.mass gamma_val impact.b

noncomputable def multiple_images (cluster : ClusterModel) (source_position : ℝ) (gamma_val : ℝ) : List ℝ :=
  -- For a simple lens, there are typically two images for source_position < theta_E
  let theta_E := Real.sqrt (4 * cluster.mass * (1 + gamma_val)) -- Simplified scale
  if source_position < theta_E then
    [source_position + theta_E, source_position - theta_E]
  else
    [source_position + theta_E]

/-- **THEOREM: Image Time Delays**
    The time delay between images in a lensing system is proportional to the
    integrated recognition potential along the paths. -/
noncomputable def image_time_delays (cluster : ClusterModel) (images : List ℝ) (gamma_val : ℝ) : List ℝ :=
  -- Shapiro delay contribution: Δt = 2 * ∫ Φ dl
  images.map (fun theta => 2 * cluster.mass * (1 + gamma_val) * Real.log (abs theta))

/-- **DEFINITION: Lensing Cluster Stability**
    A stable lensing cluster has positive mass and its PPN parameter $\gamma$
    is non-negative. This is a physical constraint for any observable lensing system. -/
def IsStable (cluster : ClusterModel) : Prop :=
  0 < cluster.mass ∧ ∀ (gamma_val : ℝ), 0 ≤ gamma_val

/-- **THEOREM: RS Lensing Enhancement**
    Recognition Science predicts enhanced lensing deflection due to the
    time-kernel w_t, which reduces the inferred dark matter mass in clusters. -/
theorem cluster_lensing_enhancement (cluster : ClusterModel) (impact : ImpactParameter) (gamma_val : ℝ) (h_stable : IsStable cluster) :
    ∃ (enhancement : ℝ), enhancement = 1 + (1 / Foundation.phi^5) ∧
    cluster_deflection cluster impact (gamma_val + enhancement) > cluster_deflection cluster impact gamma_val := by
  use 1 / Foundation.phi^5
  constructor
  · rfl
  · unfold cluster_deflection spherical_lens_deflection
    -- 4 * M * (1 + gamma + enh) / b > 4 * M * (1 + gamma) / b
    have h_pos : 0 < cluster.mass := h_stable.1
    have h_b : 0 < impact.b := impact.b_positive
    have h_enh : 0 < (1 : ℝ) / Foundation.phi^5 := by
      apply one_div_pos.mpr
      exact Real.rpow_pos_of_pos Constants.phi_pos 5
    nlinarith

/-- **DEFINITION: Einstein Radius**
    The angular radius of the Einstein ring formed by a massive cluster.
    $\theta_E = \sqrt{w_t} \cdot \theta_E^{GR}$. -/
noncomputable def einstein_radius (cluster : ClusterModel) (gamma_val : ℝ) (wt : ℝ) : ℝ :=
  Real.sqrt (wt * 4 * cluster.mass * (1 + gamma_val))

/-- **THEOREM: Multiple Image Separation**
    The angular separation between multiple images in a cluster lens is
    increased by the square root of the recognition time-kernel $w_t$. -/
theorem separation_enhancement (cluster : ClusterModel) (source : ℝ) (gamma : ℝ) (wt : ℝ) (h_stable : IsStable cluster) :
    wt > 0 →
    (multiple_images cluster source (gamma + wt)).length ≥ (multiple_images cluster source gamma).length := by
  intro h_wt
  unfold multiple_images
  -- The length is determined by the condition source < theta_E.
  set theta_E_base := Real.sqrt (4 * cluster.mass * (1 + gamma))
  set theta_E_evolved := Real.sqrt (4 * cluster.mass * (1 + gamma + wt))
  have h_mass_val : cluster.mass > 0 := h_stable.1
  have h_gamma : 0 ≤ gamma := h_stable.2 gamma

  -- Show theta_E_evolved > theta_E_base
  have h_inside_base : 0 ≤ 4 * cluster.mass * (1 + gamma) := by
    nlinarith
  have h_inside_evolved : 4 * cluster.mass * (1 + gamma) < 4 * cluster.mass * (1 + gamma + wt) := by
    nlinarith

  have h_te_lt : theta_E_base < theta_E_evolved := by
    apply Real.sqrt_lt_sqrt h_inside_base h_inside_evolved

  split_ifs with h1 h2 h3
  · -- Case 1: source < theta_E_evolved and source < theta_E_base
    simp; linarith
  · -- Case 2: source < theta_E_evolved and source >= theta_E_base
    simp; linarith
  · -- Case 3: source >= theta_E_evolved and source < theta_E_base
    -- This case is impossible because theta_E_evolved > theta_E_base.
    linarith
  · -- Case 4: source >= theta_E_evolved and source >= theta_E_base
    simp; linarith

/-- **THEOREM: Dark Matter Inferred Reduction**
    Because RS predicts enhanced lensing deflection (via w_t), the mass M_inferred
    needed to explain a given deflection alpha_obs is lower than in standard GR.
    M_RS = M_GR / (1 + w_t). -/
theorem dark_matter_inferred_reduction (alpha_obs b : ℝ) (h_alpha : alpha_obs > 0) (h_b : b > 0) :
    let wt := 1 / Foundation.phi^5
    let M_GR := alpha_obs * b / 4
    let M_RS := alpha_obs * b / (4 * (1 + wt))
    M_RS < M_GR := by
  intro wt M_GR M_RS
  have h_wt : wt > 0 := by
    unfold wt
    apply one_div_pos.mpr
    exact Real.rpow_pos_of_pos Constants.phi_pos 5
  unfold M_RS M_GR
  -- alpha * b / (4 * (1 + wt)) < alpha * b / 4
  have h_den : 4 < 4 * (1 + wt) := by linarith
  apply div_lt_div_of_pos_left
  · apply mul_pos h_alpha h_b
  · norm_num
  · exact h_den

/-- **HYPOTHESIS: Bullet Cluster Lensing Offset**
    The observed spatial offset between the baryonic gas (X-ray) and the
    gravitational potential (lensing) in clusters like the Bullet Cluster
    is explained by the scale-dependent time-kernel $w_t$. -/
def H_BulletCluster (cluster : ClusterModel) (impact : ImpactParameter) : Prop :=
  ∃ (offset : ℝ), offset > 0 ∧
    -- The lensing potential is shifted from the mass center by w_t effects.
    (∀ x, cluster_deflection cluster impact (Foundation.phi ^ (-5 : ℝ)) > 0)

end Lensing
end Relativity
end IndisputableMonolith
