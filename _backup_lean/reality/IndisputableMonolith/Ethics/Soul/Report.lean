/-!
# Soul Report

Lightweight reporting utilities for `SoulCharacter` and audit bundles suitable
for logs, dashboards, or machine ingestion.
-/

import IndisputableMonolith.Ethics.Soul.Character
import IndisputableMonolith.Ethics.Audit

namespace IndisputableMonolith
namespace Ethics
namespace Soul
namespace Report

open Soul

/-- Render a concise, single-line summary. -/
def summarize
    {AgentId BondId : Type}
    (sc : SoulCharacter AgentId BondId) : String :=
  s!"Z={sc.zInvariant} σ={sc.sigmaLedger.sigmaCurrent} V={sc.valueProfile.value} MI={sc.valueProfile.mutualInformation} C_J*={sc.valueProfile.curvaturePenalty} λ₂={sc.robustness.lambda2}"

/-- Emit a minimal JSON-like string (not a full JSON library). -/
def toJson
    {AgentId BondId : Type}
    (sc : SoulCharacter AgentId BondId) : String :=
  "{" ++
  s!"\"Z\":{sc.zInvariant}," ++
  s!"\"sigma\":{sc.sigmaLedger.sigmaCurrent}," ++
  s!"\"V\":{sc.valueProfile.value}," ++
  s!"\"MI\":{sc.valueProfile.mutualInformation}," ++
  s!"\"C_J_star\":{sc.valueProfile.curvaturePenalty}," ++
  s!"\"lambda2\":{sc.robustness.lambda2}," ++
  s!"\"time_to_balance\":{match sc.trajectoryIntegrals.timeToBalance with | some n => toString n | none => "null"}" ++
  "}"

/-- Render the audit trajectory (if available) as a multi-line string. -/
def trajectoryReport (audit : Audit.VirtueAudit) : String :=
  let rows :=
    audit.trajectory.enum.map (fun ⟨idx, sample⟩ =>
      s!"tick {idx}: σ={sample.sigma}, ΔS_max={sample.max_harm}, welfare={sample.welfare}, λ₂={sample.lambda2}")
  match rows with
  | [] => "(no trajectory samples)"
  | _  => String.intercalate "\n" rows

/-- Summarize redemption (σ trend) and robustness change. -/
def trendReport (audit : Audit.VirtueAudit) : String :=
  s!"σ: {audit.sigma_before} → {audit.sigma_after} | λ₂: {audit.spectral_gap_before} → {audit.spectral_gap_after}"

/-- High-level bundle summary combining soul and audit perspectives. -/
def bundleSummary
    {AgentId BondId : Type}
    (bundle : Audit.AuditBundle) : String :=
  let soulLine := summarize bundle.soul
  let trendLine := trendReport bundle.audit
  soulLine ++ "\n" ++ trendLine

/-- Minimal JSON-like encoding for an audit bundle (soul + key audit metrics). -/
def bundleJson
    {AgentId BondId : Type}
    (bundle : Audit.AuditBundle) : String :=
  "{" ++
  "\"soul\":" ++ toJson bundle.soul ++ "," ++
  s!"\"sigma_before\":{bundle.audit.sigma_before}," ++
  s!"\"sigma_after\":{bundle.audit.sigma_after}," ++
  s!"\"lambda2_before\":{bundle.audit.spectral_gap_before}," ++
  s!"\"lambda2_after\":{bundle.audit.spectral_gap_after}," ++
  s!"\"history_len\":{bundle.history.length}" ++
  "}"

end Report
end Soul
end Ethics
end IndisputableMonolith
