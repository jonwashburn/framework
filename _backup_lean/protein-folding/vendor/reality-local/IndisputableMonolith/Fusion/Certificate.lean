import Mathlib
import IndisputableMonolith.Fusion.Scheduler
import IndisputableMonolith.Fusion.SymmetryLedger

/-!
# Certificate Layer

Certificate layer gluing the phi-scheduler execution to symmetry-ledger
evaluations. A certificate bundles ledger thresholds, per-mode bounds, and the
compiled schedule so we can state a unified pass predicate.
-/
namespace IndisputableMonolith
namespace Fusion

open scoped BigOperators
open Classical

noncomputable section

structure Certificate (Actuator Mode : Type _) [Fintype Mode] [DecidableEq Mode]
    (L : ℕ) where
  scheduler : PhiScheduler Actuator L
  ledgerCfg : LedgerConfig (Mode := Mode)
  bounds : ModeThresholds (Mode := Mode)
  ledgerThreshold : ℝ
  ledgerThreshold_nonneg : 0 ≤ ledgerThreshold

variable {Actuator Mode : Type _} [Fintype Mode] [DecidableEq Mode]
variable {L : ℕ}

namespace Certificate

variable (cert : Certificate (Actuator := Actuator) (Mode := Mode) L)

def passes (ratios : ModeRatios (Mode := Mode)) : Prop :=
  Fusion.pass cert.ledgerCfg cert.bounds cert.ledgerThreshold ratios

def authorizes (exec : cert.scheduler.Execution) (ratios : ModeRatios (Mode := Mode)) : Prop :=
  cert.passes ratios

lemma authorizes_of_unity
    (exec : cert.scheduler.Execution) (ratios : ModeRatios (Mode := Mode))
    (hunity : ratios.isUnity)
    (hbound : ∀ m, 1 ≤ cert.bounds.upper m) :
    cert.authorizes exec ratios := by
  unfold authorizes passes
  exact unity_pass (cfg := cert.ledgerCfg)
    (bounds := cert.bounds) (Λ := cert.ledgerThreshold) (r := ratios) hunity
    cert.ledgerThreshold_nonneg hbound

end Certificate

end

end Fusion
end IndisputableMonolith
