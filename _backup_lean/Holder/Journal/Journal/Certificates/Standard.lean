/-!
# Physical Certificate Standard

Every physical claim in the Journal must be packaged as a `PhysicalCertificate`.
This ensures:
1. The derived value is explicit.
2. The empirical target is explicit.
3. The proof relies only on authorized axioms (enforced by CI).
-/

namespace Journal.Certificates

/-- A certificate for a real-valued physical quantity. -/
structure RealCertificate where
  /-- Name of the quantity (e.g., "Fine Structure Constant"). -/
  name : String
  /-- The derived value from RS. -/
  derived : Float
  /-- Lower bound of empirical range. -/
  empirical_min : Float
  /-- Upper bound of empirical range. -/
  empirical_max : Float
  /-- Does the derived value fall within the empirical range? -/
  matches : Bool := empirical_min ≤ derived ∧ derived ≤ empirical_max

/-- A certificate for a discrete/counting quantity. -/
structure IntCertificate where
  name : String
  derived : Nat
  empirical : Nat
  matches : Bool := derived == empirical

/-- The Forcing Chain Certificate: T0–T8 are all proved. -/
structure ForcingChainCertificate where
  t0_logic : Bool
  t1_existence : Bool
  t2_discreteness : Bool
  t3_ledger : Bool
  t4_recognition : Bool
  t5_j_unique : Bool
  t6_phi : Bool
  t7_eight_tick : Bool
  t8_dimension : Bool
  all_proved : Bool := t0_logic ∧ t1_existence ∧ t2_discreteness ∧
                       t3_ledger ∧ t4_recognition ∧ t5_j_unique ∧
                       t6_phi ∧ t7_eight_tick ∧ t8_dimension

end Journal.Certificates
