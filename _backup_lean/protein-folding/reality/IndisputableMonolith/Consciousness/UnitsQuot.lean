import Mathlib
import IndisputableMonolith.Consciousness.Equivalence

/‑!
# Units Quotient for Photon Channels

Upgrade units equivalence (`~U`) on `PhotonChannel` to a `Setoid` and define
the quotient object. Provide a uniqueness lemma stating that the CP → PC witness
is unique as an object in the quotient category (initial/terminal up to ~U).
-/

namespace IndisputableMonolith
namespace Consciousness

/-- Setoid induced by units/bridge equivalence on `PhotonChannel`. -/
instance photonChannelUnitsSetoid : Setoid PhotonChannel where
  r := UnitsEquiv
  iseqv := {
    refl := units_equiv_refl
    symm := units_equiv_symm
    trans := units_equiv_trans
  }

/-- Quotient of photon channels by units equivalence (~U). -/
abbrev PhotonChannelU := Quot UnitsEquiv

/-- Uniqueness of the CP → PC witness in the units quotient.

Given a well-formed `cp` and two well-formed photon channels `pc1, pc2` that
agree with `cp` on units and bridge, their images in the quotient coincide. -/
theorem photon_channel_unique_initial_up_to_units
  (cp : ConsciousProcess) [ConsciousProcess.WellFormed cp]
  (pc1 pc2 : PhotonChannel)
  [PhotonChannel.WellFormed pc1] [PhotonChannel.WellFormed pc2]
  (h1u : pc1.units = cp.units) (h2u : pc2.units = cp.units)
  (h1b : pc1.bridge = cp.bridge) (h2b : pc2.bridge = cp.bridge) :
  (Quot.mk UnitsEquiv pc1) = (Quot.mk UnitsEquiv pc2) := by
  -- They are ~U-equivalent; hence equal in the quotient
  apply Quot.sound
  refine ⟨?hu, ?hb⟩
  · -- Units coincide
    exact h1u.trans h2u.symm
  · -- Bridge coincide
    exact h1b.trans h2b.symm

end Consciousness
end IndisputableMonolith
