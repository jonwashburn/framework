bNoncomputable def trivGaugeFacts : GaugeConstructionFacts :=
{ find_gauge_vector_for_newtonian := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ h; simp [gauge_transform, InNewtonianGauge]⟩
, spatial_trace_freedom := by intro h hnewt; exact ⟨⟨fun _ => 0⟩, hnewt, by intro _ _ _ _ _ _; simp [gauge_transform, InNewtonianGauge]⟩
, newtonian_gauge_exists := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
, matched_to_newtonian_gauge := by intro h hWF; exact ⟨⟨⟨fun _ => 0⟩, 0, le_rfl, le_of_eq rfl, by intro _ _ _; simp⟩, by intro _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
, gauge_invariant_riemann := by intro g₀ h ξ x ρ σ μ ν; simp [gauge_transform, linearized_riemann]
, test_newtonian_gauge_construction := by intro h ng x i hi; simp [gauge_transform, to_newtonian_gauge, hi] }

noncomputable instance : GaugeConstructionFacts := trivGaugeFacts
