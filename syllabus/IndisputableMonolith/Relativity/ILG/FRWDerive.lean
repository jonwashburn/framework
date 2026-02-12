import Mathlib
import IndisputableMonolith.Relativity/ILG/FRW
import IndisputableMonolith.Relativity/ILG/Action

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- ψ stress-energy 00-component placeholder. -/
noncomputable def Tpsi00 (p : ILGParams) : ℝ := rho_psi p

/-- Link: FriedmannI can be satisfied by choosing H^2 = Tpsi00 (symbolic). -/
theorem friedmann_from_Tpsi (t : ℝ) (p : ILGParams) :
  FriedmannI t p ↔ (H t) ^ 2 = Tpsi00 p := Iff.rfl

end ILG
end Relativity
end IndisputableMonolith
