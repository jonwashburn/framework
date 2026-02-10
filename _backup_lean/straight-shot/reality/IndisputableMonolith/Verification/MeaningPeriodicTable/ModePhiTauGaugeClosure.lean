import IndisputableMonolith.Verification.MeaningPeriodicTable.ModePhiClosure
import IndisputableMonolith.Token.WTokenBasis

/-!
# Mode+Φ+τ (Gauge) Closure

This is the “next closure step” after `ModePhiClosure`:

- `ModePhiClosure` forces **mode family** (from the basis-class classifier) and forces
  **φ-level** (from the RS reference-cost projection `projectOntoPhiLattice`).

- This module adds the third component **τ-offset / gauge data** and proves:

> **τ is forced only up to global phase gauge.**

Concretely, for the self-conjugate mode-4 family, the τ₂ basis is obtained from τ₀ by
multiplication by `i`, so τ₀ vs τ₂ are not gauge-invariantly distinguishable by any
construction that is invariant under global phase.

We formalize this as a *phase equivalence* relation `PhaseEq` on `ℂ⁸` vectors and prove that
any two τ-variants extending the same `(modeFamily, φLevel)` are `PhaseEq`.
-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningPeriodicTable

open scoped Classical

/-! ## Phase / gauge equivalence on `ℂ⁸` -/

/-- Two `ℂ⁸` vectors are *phase / gauge equivalent* if they differ by multiplication
by a unit-modulus complex scalar. -/
def PhaseEq (v₁ v₂ : Fin 8 → ℂ) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ v₂ = fun t => c * v₁ t

lemma phaseEq_refl (v : Fin 8 → ℂ) : PhaseEq v v :=
  ⟨1, by simp, by ext t; simp⟩

lemma phaseEq_symm {v₁ v₂ : Fin 8 → ℂ} (h : PhaseEq v₁ v₂) : PhaseEq v₂ v₁ := by
  rcases h with ⟨c, hc, rfl⟩
  -- `v₂ = c • v₁`, so `v₁ = c⁻¹ • v₂` and `‖c⁻¹‖² = 1`.
  have hc0 : c ≠ 0 := by
    intro h0
    have : (0 : ℝ) = 1 := by simpa [h0] using hc
    exact zero_ne_one this
  refine ⟨c⁻¹, ?_, ?_⟩
  · -- normSq (c⁻¹) = 1
    -- Use multiplicativity: normSq(c * c⁻¹) = normSq c * normSq c⁻¹ = normSq 1 = 1.
    have hmul : Complex.normSq (c * c⁻¹) = Complex.normSq c * Complex.normSq (c⁻¹) := by
      simpa using (Complex.normSq_mul c c⁻¹)
    have hcc : c * c⁻¹ = 1 := by simp [hc0]
    have : (1 : ℝ) = Complex.normSq c * Complex.normSq (c⁻¹) := by
      -- `Complex.normSq 1 = 1`.
      simpa [hcc] using hmul
    have : (1 : ℝ) = Complex.normSq (c⁻¹) := by
      simpa [hc] using this
    exact this.symm
  · -- pointwise equality
    ext t
    simp [mul_assoc, hc0]

lemma phaseEq_trans {v₁ v₂ v₃ : Fin 8 → ℂ} (h₁₂ : PhaseEq v₁ v₂) (h₂₃ : PhaseEq v₂ v₃) :
    PhaseEq v₁ v₃ := by
  rcases h₁₂ with ⟨c₁, hc₁, rfl⟩
  rcases h₂₃ with ⟨c₂, hc₂, rfl⟩
  refine ⟨c₂ * c₁, ?_, ?_⟩
  · -- normSq (c₂*c₁)=1
    simpa [hc₁, hc₂] using (Complex.normSq_mul c₂ c₁)
  · ext t
    simp [mul_assoc]

def phaseSetoid : Setoid (Fin 8 → ℂ) where
  r := PhaseEq
  iseqv := ⟨phaseEq_refl, @phaseEq_symm, @phaseEq_trans⟩

abbrev PhaseClass : Type :=
  Quotient phaseSetoid

/-! ## The τ-extended signature -/

structure ModePhiTauSignature extends ModePhiSignature where
  tauVariant : Water.TauOffset
  tau_legal : modeFamily ≠ Water.WTokenMode.mode4 → tauVariant = Water.TauOffset.tau0
  deriving Repr

def ModePhiTauSignature.toSpec (s : ModePhiTauSignature) : Water.WTokenSpec :=
  ⟨s.modeFamily, s.phiLevel, s.tauVariant, s.tau_legal⟩

noncomputable def ModePhiTauSignature.tokenId (s : ModePhiTauSignature) : Token.WTokenId :=
  Token.WTokenId.ofSpec s.toSpec

noncomputable def ModePhiTauSignature.basis (s : ModePhiTauSignature) : Fin 8 → ℂ :=
  Token.WTokenId.basisOfId s.tokenId

def ModePhiTauSignature.normalizeTau (s : ModePhiTauSignature) : ModePhiTauSignature :=
  { modeFamily := s.modeFamily
    phiLevel := s.phiLevel
    tauVariant := Water.TauOffset.tau0
    tau_legal := by intro _; rfl }

/-! ## Core lemma: τ is unique up to gauge at fixed mode+φ -/

theorem tau_forced_up_to_gauge
    (m : Water.WTokenMode) (phi : Water.PhiLevel)
    (tau tau' : Water.TauOffset)
    (hτ : m ≠ Water.WTokenMode.mode4 → tau = Water.TauOffset.tau0)
    (hτ' : m ≠ Water.WTokenMode.mode4 → tau' = Water.TauOffset.tau0) :
    PhaseEq
      (Token.WTokenId.basisOfId (Token.WTokenId.ofSpec ⟨m, phi, tau, hτ⟩))
      (Token.WTokenId.basisOfId (Token.WTokenId.ofSpec ⟨m, phi, tau', hτ'⟩)) := by
  -- `basisOfId` depends only on `(mode, tau)`; `phi` plays no role in the waveform model.
  cases m with
  | mode1_7 =>
      -- For non-self-conjugate families, legality forces τ = τ0.
      have ht : tau = Water.TauOffset.tau0 := hτ (by decide)
      have ht' : tau' = Water.TauOffset.tau0 := hτ' (by decide)
      subst ht; subst ht'
      refine ⟨1, by simp, ?_⟩
      ext t
      simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]
  | mode2_6 =>
      have ht : tau = Water.TauOffset.tau0 := hτ (by decide)
      have ht' : tau' = Water.TauOffset.tau0 := hτ' (by decide)
      subst ht; subst ht'
      refine ⟨1, by simp, ?_⟩
      ext t
      simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]
  | mode3_5 =>
      have ht : tau = Water.TauOffset.tau0 := hτ (by decide)
      have ht' : tau' = Water.TauOffset.tau0 := hτ' (by decide)
      subst ht; subst ht'
      refine ⟨1, by simp, ?_⟩
      ext t
      simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]
  | mode4 =>
      -- The self-conjugate family has two τ-variants; they differ by a phase factor `±i`.
      cases tau <;> cases tau'
      · -- τ0 / τ0
        refine ⟨1, by simp, ?_⟩
        ext t
        simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]
      · -- τ0 / τ2
        refine ⟨Complex.I, by simp [Complex.normSq_I], ?_⟩
        ext t
        simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily, mul_assoc]
      · -- τ2 / τ0  (use `-i`, since (-i) * (i * x) = x)
        refine ⟨-Complex.I, by simp [Complex.normSq_I], ?_⟩
        ext t
        -- After unfolding, this reduces to `dft8_mode 4 t = - (I * (I * dft8_mode 4 t))`,
        -- which is true since `I*I = -1`.
        simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]
        have hassoc :
            Complex.I * (Complex.I * LightLanguage.Basis.dft8_mode 4 t) =
              (Complex.I * Complex.I) * LightLanguage.Basis.dft8_mode 4 t := by
          simpa using (mul_assoc Complex.I Complex.I (LightLanguage.Basis.dft8_mode 4 t)).symm
        have hphase :
            -(Complex.I * (Complex.I * LightLanguage.Basis.dft8_mode 4 t)) =
              LightLanguage.Basis.dft8_mode 4 t := by
          calc
            -(Complex.I * (Complex.I * LightLanguage.Basis.dft8_mode 4 t))
                = -((Complex.I * Complex.I) * LightLanguage.Basis.dft8_mode 4 t) := by
                    simpa [hassoc]
            _ = -((-1 : ℂ) * LightLanguage.Basis.dft8_mode 4 t) := by
                    simp [Complex.I_mul_I]
            _ = LightLanguage.Basis.dft8_mode 4 t := by
                    simp
        exact hphase.symm
      · -- τ2 / τ2
        refine ⟨1, by simp, ?_⟩
        ext t
        simp [Token.WTokenId.basisOfId, Token.WTokenId.dftModeOfFamily]

/-! ## “Forced up to gauge” uniqueness for τ-extensions of a fixed `(modeFamily, φLevel)` -/

def ModePhiTauSignature.GaugeEq (s s' : ModePhiTauSignature) : Prop :=
  s.modeFamily = s'.modeFamily ∧
  s.phiLevel = s'.phiLevel ∧
  PhaseEq s.basis s'.basis

lemma ModePhiTauSignature.gaugeEq_refl (s : ModePhiTauSignature) :
    ModePhiTauSignature.GaugeEq s s := by
  refine ⟨rfl, rfl, ?_⟩
  exact phaseEq_refl _

lemma ModePhiTauSignature.gaugeEq_symm {s s' : ModePhiTauSignature}
    (h : ModePhiTauSignature.GaugeEq s s') :
    ModePhiTauSignature.GaugeEq s' s := by
  rcases h with ⟨hm, hphi, hphase⟩
  refine ⟨hm.symm, hphi.symm, ?_⟩
  exact phaseEq_symm hphase

lemma ModePhiTauSignature.gaugeEq_trans {s₁ s₂ s₃ : ModePhiTauSignature}
    (h₁₂ : ModePhiTauSignature.GaugeEq s₁ s₂)
    (h₂₃ : ModePhiTauSignature.GaugeEq s₂ s₃) :
    ModePhiTauSignature.GaugeEq s₁ s₃ := by
  rcases h₁₂ with ⟨hm12, hphi12, hphase12⟩
  rcases h₂₃ with ⟨hm23, hphi23, hphase23⟩
  refine ⟨hm12.trans hm23, hphi12.trans hphi23, ?_⟩
  exact phaseEq_trans hphase12 hphase23

theorem ModePhiTauSignature.gaugeEq_equivalence :
    Equivalence ModePhiTauSignature.GaugeEq :=
  ⟨ModePhiTauSignature.gaugeEq_refl,
   @ModePhiTauSignature.gaugeEq_symm,
   @ModePhiTauSignature.gaugeEq_trans⟩

def ModePhiTauSignature.gaugeSetoid : Setoid ModePhiTauSignature where
  r := ModePhiTauSignature.GaugeEq
  iseqv := ModePhiTauSignature.gaugeEq_equivalence

/-- “τ modulo gauge”: the quotient of `ModePhiTauSignature` by gauge equivalence. -/
abbrev TauModuloGauge : Type :=
  Quotient ModePhiTauSignature.gaugeSetoid

def ModePhiTauSignature.tauModGauge (s : ModePhiTauSignature) : TauModuloGauge :=
  Quotient.mk (s := ModePhiTauSignature.gaugeSetoid) s

theorem ModePhiTauSignature.tauModGauge_eq_iff (s s' : ModePhiTauSignature) :
    s.tauModGauge = s'.tauModGauge ↔ ModePhiTauSignature.GaugeEq s s' := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

noncomputable def TauModuloGauge.normalForm : TauModuloGauge → ModePhiTauSignature :=
  Quotient.lift
    (s := ModePhiTauSignature.gaugeSetoid)
    (fun s => s.normalizeTau)
    (by
      intro a b hab
      rcases hab with ⟨hm, hphi, _hphase⟩
      -- `normalizeTau` depends only on `(modeFamily, phiLevel)`.
      -- Use `hm` and `hphi` to rewrite.
      cases a with
      | mk abase atau atau_legal =>
        cases abase with
        | mk am aphi =>
          cases b with
          | mk bbase btau btau_legal =>
            cases bbase with
            | mk bm bphi =>
              have hm' : am = bm := by simpa using hm
              have hphi' : aphi = bphi := by simpa using hphi
              cases hm'
              cases hphi'
              rfl)

theorem ModePhiTauSignature.gaugeEq_normalizeTau (s : ModePhiTauSignature) :
    ModePhiTauSignature.GaugeEq s s.normalizeTau := by
  refine ⟨rfl, rfl, ?_⟩
  -- Use the core lemma with τ' = τ0 (the canonical representative).
  simpa [ModePhiTauSignature.basis, ModePhiTauSignature.tokenId, ModePhiTauSignature.toSpec,
    ModePhiTauSignature.normalizeTau] using
    (tau_forced_up_to_gauge s.modeFamily s.phiLevel s.tauVariant Water.TauOffset.tau0 s.tau_legal
      (by intro _; rfl))

theorem ModePhiTauSignature.tauModGauge_normalizeTau (s : ModePhiTauSignature) :
    s.tauModGauge = s.normalizeTau.tauModGauge := by
  exact (ModePhiTauSignature.tauModGauge_eq_iff s s.normalizeTau).2 (gaugeEq_normalizeTau s)

theorem ModePhiTauSignature.gaugeEq_of_same_modePhi
    (s s' : ModePhiTauSignature)
    (hm : s.modeFamily = s'.modeFamily)
    (hphi : s.phiLevel = s'.phiLevel) :
    ModePhiTauSignature.GaugeEq s s' := by
  refine ⟨hm, hphi, ?_⟩
  -- Reduce to the parameter-level lemma `tau_forced_up_to_gauge`.
  -- We destruct `s`/`s'` so the `(modeFamily, phiLevel)` equalities become plain variable equalities
  -- (this avoids dependent-elimination issues from structure extension projections).
  cases s with
  | mk sBase tau tau_legal =>
    cases sBase with
    | mk m phi =>
      cases s' with
      | mk sBase' tau' tau_legal' =>
        cases sBase' with
        | mk m' phi' =>
          -- `hm : m = m'` and `hphi : phi = phi'` after unfolding projections.
          -- (Use `simp` to rewrite the projections into the variables we just introduced.)
          have hm' : m = m' := by simpa using hm
          have hphi' : phi = phi' := by simpa using hphi
          cases hm'
          cases hphi'
          -- Now apply the generic τ-gauge lemma at fixed parameters.
          simpa [ModePhiTauSignature.basis, ModePhiTauSignature.tokenId, ModePhiTauSignature.toSpec] using
            (tau_forced_up_to_gauge m phi tau tau' tau_legal tau_legal')

/-! ## Optional: a concrete forcing function from inputs (v, r)

This mirrors the earlier closure pattern: mode is read from the classifier, φ-level from RS projection,
and τ is whatever representative is returned by the classifier (not gauge-invariant by itself).

The correctness theorem you should use downstream is *not* “τ is uniquely forced”, but the
`gaugeEq_of_same_modePhi` theorem above (uniqueness up to gauge).
-/

noncomputable def forcedModePhiTauSignature
    (v : Fin 8 → ℂ) (r : ℝ) (hr : 0 < r) : Option ModePhiTauSignature :=
  match classify v with
  | .exact w =>
      let spec := Token.WTokenId.toSpec w
      some
        { modeFamily := spec.mode
          phiLevel := forcedPhiLevel r hr
          tauVariant := spec.tau_offset
          tau_legal := spec.tau_valid }
  | .ambiguous => none
  | .invalid => none

end MeaningPeriodicTable
end Verification
end IndisputableMonolith
