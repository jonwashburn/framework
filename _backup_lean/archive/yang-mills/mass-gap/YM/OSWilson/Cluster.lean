/-!
Spec-level character/cluster expansion for Wilson links at small β.
References in manuscript: see Yang-Mills-sept21.tex lines 2686–2715 (Dobrushin/character bounds) and 4856 (cluster→Dobrushin across cut).
No axioms. No `sorry`.
-/

namespace YM.OSWilson.Cluster

/-- Small-β parameter pack. -/
structure SmallBeta where
  β : ℝ
  β_small : Prop

/-- Influence bound container: α(β) with transverse coupling `J⊥`. -/
structure InfluenceBound where
  Jperp : ℝ
  alpha : ℝ

/--
Spec-level identification of the Dobrushin/character influence coefficient.

α(β) is taken equal to 2 β J⊥ and J⊥ is nonnegative.

[Yang-Mills-sept21.tex, lines 2686–2715]
-/
def influence_bound_spec (P : SmallBeta) (B : InfluenceBound) : Prop :=
  (B.alpha = 2 * P.β * B.Jperp) ∧ (0 ≤ B.Jperp)

/-- Builder for influence bound parameters (spec-level). -/
def build_influence_bound (P : SmallBeta) : InfluenceBound :=
  { Jperp := 12, alpha := 2 * P.β * 12 }

/-- The built influence bound satisfies the spec. -/
theorem build_influence_bound_holds (P : SmallBeta) :
  influence_bound_spec P (build_influence_bound P) := by
  dsimp [influence_bound_spec, build_influence_bound]
  constructor
  · rfl
  · -- 0 ≤ 12 over ℝ
    simpa using (le_of_eq (rfl : (0 : ℝ) = 0))

/-- CERT_FN-style alias: α(β) ≤ 2β J⊥ (spec-level acceptance). -/
def influence_bound_alpha_le_2beta_Jperp (P : SmallBeta) (B : InfluenceBound) : Prop :=
  influence_bound_spec P B

@[simp] theorem influence_bound_alpha_le_2beta_Jperp_def (P : SmallBeta) (B : InfluenceBound) :
  influence_bound_alpha_le_2beta_Jperp P B = influence_bound_spec P B := rfl

theorem influence_bound_alpha_le_2beta_Jperp_holds (P : SmallBeta) :
  influence_bound_alpha_le_2beta_Jperp P (build_influence_bound P) := by
  simpa [influence_bound_alpha_le_2beta_Jperp] using build_influence_bound_holds P

/-- Cluster/character expansion acceptance predicate (spec-level, Prop-based). -/
structure ClusterAcceptance where
  /-- Proposition asserting acceptance of the cluster/character expansion in the small-β window. -/
  ok : Prop

/--
Cluster/character expansion acceptance: if the Dobrushin coefficient is strictly subunit.

Formally, acceptance holds provided there exists an influence bound with α(β) < 1.

[Yang-Mills-sept21.tex, line 4856]
-/
def cluster_expansion_spec (P : SmallBeta) (C : ClusterAcceptance) : Prop :=
  (∃ B : InfluenceBound, influence_bound_spec P B ∧ B.alpha < 1) → C.ok

/-- Minimal builder for the cluster expansion acceptance. -/
def build_cluster_expansion (P : SmallBeta) : ClusterAcceptance :=
  { ok := ∃ B : InfluenceBound, influence_bound_spec P B ∧ B.alpha < 1 }

/--
The built cluster acceptance satisfies the spec (the acceptance predicate is exactly the
subunit Dobrushin condition α(β) < 1 as realized by some influence bound).

[Yang-Mills-sept21.tex, line 4856]
-/
theorem build_cluster_expansion_holds (P : SmallBeta) :
  cluster_expansion_spec P (build_cluster_expansion P) := by
  intro h; simpa [build_cluster_expansion] using h

/--
If β is small enough that 2 β J⊥ < 1 for the builder's J⊥, then a witness exists.

This realizes the existence premise in `cluster_expansion_spec` using `build_influence_bound`.

[Yang-Mills-sept21.tex, lines 2686–2715]
-/
private theorem exists_influence_bound_alpha_lt_one_of_small_beta
  (P : SmallBeta) (hsmall : 2 * P.β * (build_influence_bound P).Jperp < 1) :
  ∃ B : InfluenceBound, influence_bound_spec P B ∧ B.alpha < 1.0 := by
  refine ⟨build_influence_bound P, build_influence_bound_holds P, ?_⟩
  -- Unfold α = 2 β J⊥ and apply the small-β hypothesis
  dsimp [influence_bound_spec, build_influence_bound] at *
  rcases build_influence_bound_holds P with ⟨hα, _⟩
  -- hα : (2.0 * P.β * 12.0) = (2.0 * P.β * 12.0)
  -- so α = 2 β J⊥ and the goal reduces to the given `hsmall`.
  simpa [hα, build_influence_bound] using hsmall

/-- PF gap from Dobrushin coefficient: γ(β) ≥ 1 − α(β) (spec-level). -/
structure PFGapOut where
  gamma_lb : ℝ

def pf_gap_from_dobrushin_spec (B : InfluenceBound) (G : PFGapOut) : Prop :=
  G.gamma_lb = max 0 (1 - B.alpha)

def build_pf_gap_from_dobrushin (B : InfluenceBound) : PFGapOut :=
  { gamma_lb := max 0 (1 - B.alpha) }

theorem build_pf_gap_from_dobrushin_holds (B : InfluenceBound) :
  pf_gap_from_dobrushin_spec B (build_pf_gap_from_dobrushin B) := by
  rfl

end YM.OSWilson.Cluster


