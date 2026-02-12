import Mathlib
import IndisputableMonolith.Relativity/ILG/Compact

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Horizon proxy: use ilg_bh_radius compared to baseline. -/
noncomputable def horizon_proxy (M : ℝ) (p : ILGParams) : ℝ :=
  ilg_bh_radius M p.cLag p.alpha

/-- Ringdown proxy: proportional to 1 / radius (toy). -/
noncomputable def ringdown_proxy (M : ℝ) (p : ILGParams) : ℝ :=
  1 / (horizon_proxy M p)

theorem horizon_band (M κ : ℝ) (p : ILGParams) (hκ : 0 ≤ κ) :
  |horizon_proxy M p - baseline_bh_radius M| ≤ κ := by
  simpa [horizon_proxy] using bh_static_band M κ p.cLag p.alpha hκ

end ILG
end Relativity
end IndisputableMonolith
