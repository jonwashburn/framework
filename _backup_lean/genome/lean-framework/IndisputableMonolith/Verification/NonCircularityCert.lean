import Mathlib
import IndisputableMonolith.Constants.KDisplayCore
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.URCGenerators.Family
import IndisputableMonolith.URCGenerators.CPMMethodCert
import IndisputableMonolith.Verification.AdvancedParticlePhysicsCert
import IndisputableMonolith.Verification.AlphaDerivationCert
import IndisputableMonolith.Verification.AnchorsRescaleEqvCert
import IndisputableMonolith.Verification.AxiomaticOpsCert
import IndisputableMonolith.Verification.BandsInvariantCert
import IndisputableMonolith.Verification.BornRuleDerivationCert
import IndisputableMonolith.Verification.CPMConstantsCert
import IndisputableMonolith.Verification.CalibrationCert
import IndisputableMonolith.Verification.CminDerivationCert
import IndisputableMonolith.Verification.ConjTransposeShiftMulCert
import IndisputableMonolith.Verification.ConvexityCert
import IndisputableMonolith.Verification.CosmologyCert
import IndisputableMonolith.Verification.CoshPropertiesCert
import IndisputableMonolith.Verification.CoshStrictConvexCert
import IndisputableMonolith.Verification.CostUniquenessCert
import IndisputableMonolith.Verification.CprojDerivationCert
import IndisputableMonolith.Verification.CubeGeometryCert
import IndisputableMonolith.Verification.CurvatureSpaceCert
import IndisputableMonolith.Verification.DAlembertSymmetryCert
import IndisputableMonolith.Verification.DFT8ColumnOrthonormalCert
import IndisputableMonolith.Verification.DFT8DiagonalizesShiftCert
import IndisputableMonolith.Verification.DFT8EntrySymCert
import IndisputableMonolith.Verification.DFT8ModeNeutralCert
import IndisputableMonolith.Verification.DFT8ModeZeroConstantCert
import IndisputableMonolith.Verification.DFT8RowOrthonormalCert
import IndisputableMonolith.Verification.DFT8ShiftDiagonalizationCert
import IndisputableMonolith.Verification.DFT8ShiftEigenvectorCert
import IndisputableMonolith.Verification.DFT8SymmetryCert
import IndisputableMonolith.Verification.DFT8UnitaryCert
import IndisputableMonolith.Verification.EightTickFundamentalCert
import IndisputableMonolith.Verification.EightTickLowerBoundCert
import IndisputableMonolith.Verification.EmpiricalHypothesesCert
import IndisputableMonolith.Verification.EulerLagrangeCert
import IndisputableMonolith.Verification.FibSubstCert
import IndisputableMonolith.Verification.Gap45DimensionCert
import IndisputableMonolith.Verification.GapWeightDerivationCert
import IndisputableMonolith.Verification.GaugeInvarianceCert
import IndisputableMonolith.Verification.GenerationTorsionCert
import IndisputableMonolith.Verification.HonestClosureCert
import IndisputableMonolith.Verification.ILGCoercivityCert
import IndisputableMonolith.Verification.JCostAtPhiCert
import IndisputableMonolith.Verification.JCostLightLanguageCert
import IndisputableMonolith.Verification.JcostAxiomsCert
import IndisputableMonolith.Verification.JcostConvexityCert
import IndisputableMonolith.Verification.JcostCoshFormCert
import IndisputableMonolith.Verification.JcostCoshIdentityCert
import IndisputableMonolith.Verification.JcostMinimumCert
import IndisputableMonolith.Verification.JcostMonoCert
import IndisputableMonolith.Verification.JcostNonnegCert
import IndisputableMonolith.Verification.JcostNormalizationCert
import IndisputableMonolith.Verification.JcostSatisfiesJensenCert
import IndisputableMonolith.Verification.JcostStrictCert
import IndisputableMonolith.Verification.JcostStrictConvexCert
import IndisputableMonolith.Verification.JcostStrictPosCert
import IndisputableMonolith.Verification.JcostSymmetryCert
import IndisputableMonolith.Verification.JlogAMGM.JlogAMGMCert
import IndisputableMonolith.Verification.JlogCosh.JlogCoshCert
import IndisputableMonolith.Verification.JlogDeriv.JlogDerivCert
import IndisputableMonolith.Verification.JlogNonneg.JlogNonnegCert
import IndisputableMonolith.Verification.JlogStrictConvex.JlogStrictConvexCert
import IndisputableMonolith.Verification.JlogZero.JlogZeroCert
import IndisputableMonolith.Verification.KDisplayDimlessCert
import IndisputableMonolith.Verification.KernelMatchCert
import IndisputableMonolith.Verification.KnetDerivationCert
import IndisputableMonolith.Verification.LNALCostAdditiveCert
import IndisputableMonolith.Verification.LambdaRecDerivationCert
import IndisputableMonolith.Verification.LedgerUniquenessCert
import IndisputableMonolith.Verification.LightLanguageBridgeCert
import IndisputableMonolith.Verification.MassLawCert
import IndisputableMonolith.Verification.MatchesEvalCert
import IndisputableMonolith.Verification.MeasurementBridgeCert
import IndisputableMonolith.Verification.MetricCurvatureCert
import IndisputableMonolith.Verification.MetricFromUnitsCert
import IndisputableMonolith.Verification.Mod8MulEqCert
import IndisputableMonolith.Verification.NeutralityProjectionCert
import IndisputableMonolith.Verification.NyquistObstructionCert
import IndisputableMonolith.Verification.ODECoshUniqueCert
import IndisputableMonolith.Verification.ODEFoundationCert
import IndisputableMonolith.Verification.Omega8AbsCert
import IndisputableMonolith.Verification.Omega8ConjugateCert
import IndisputableMonolith.Verification.Omega8InvEqPow7Cert
import IndisputableMonolith.Verification.Omega8MulInvCert
import IndisputableMonolith.Verification.Omega8Pow4Cert
import IndisputableMonolith.Verification.Omega8Pow8Cert
import IndisputableMonolith.Verification.Omega8PowerProductCert
import IndisputableMonolith.Verification.Omega8PrimitiveCert
import IndisputableMonolith.Verification.Omega8PrimitivityCert
import IndisputableMonolith.Verification.Omega8PropertiesCert
import IndisputableMonolith.Verification.OneLtPhiCert
import IndisputableMonolith.Verification.PerfectGeneticCodeCert
import IndisputableMonolith.Verification.PhiAlgebraCert
import IndisputableMonolith.Verification.PhiAlternativesFailCert
import IndisputableMonolith.Verification.PhiBoundsCert
import IndisputableMonolith.Verification.PhiClosedDefaultsCert
import IndisputableMonolith.Verification.PhiDecimalBoundsCert
import IndisputableMonolith.Verification.PhiFixedPointCert
import IndisputableMonolith.Verification.PhiIrrationalityCert
import IndisputableMonolith.Verification.PhiNeZeroCert
import IndisputableMonolith.Verification.PhiNecessityCert
import IndisputableMonolith.Verification.PhiNonDegenerateCert
import IndisputableMonolith.Verification.PhiPinnedCert
import IndisputableMonolith.Verification.PhiPositivityCert
import IndisputableMonolith.Verification.PhiPowerBoundsCert
import IndisputableMonolith.Verification.PhiSelfSimilarityCert
import IndisputableMonolith.Verification.PhiSquaredCert
import IndisputableMonolith.Verification.ProbabilityNormalizationCert
import IndisputableMonolith.Verification.RSPhysicalModelCert
import IndisputableMonolith.Verification.RSStructuralDerivationCert
import IndisputableMonolith.Verification.ReciprocalSymmetryEvenCert
import IndisputableMonolith.Verification.RecognitionComplexityCert
import IndisputableMonolith.Verification.RootsOfUnitySumCert
import IndisputableMonolith.Verification.RootsOfUnitySumZeroCert
import IndisputableMonolith.Verification.ShiftMulDFT8EntryCert
import IndisputableMonolith.Verification.StandardDFT8BasisCert
import IndisputableMonolith.Verification.StarDFT8EntryMulCert
import IndisputableMonolith.Verification.StarOmega8Cert
import IndisputableMonolith.Verification.StarOmega8MulSelfCert
import IndisputableMonolith.Verification.StarOmega8PowCert
import IndisputableMonolith.Verification.StarOmega8PowMulPowCert
import IndisputableMonolith.Verification.StarOmega8PowMulSameCert
import IndisputableMonolith.Verification.StarOmega8PowMulSelfCert
import IndisputableMonolith.Verification.StructuralDerivationGapCert
import IndisputableMonolith.Verification.StructuralPartitionCert
import IndisputableMonolith.Verification.SumStarOmega8ProdCert
import IndisputableMonolith.Verification.T5UniqueCert
import IndisputableMonolith.Verification.Tier2.Tier2Cert
import IndisputableMonolith.Verification.Tier3Cert
import IndisputableMonolith.Verification.Tier6AstrophysicsCert
import IndisputableMonolith.Verification.SimplicialFoundationCert
import IndisputableMonolith.Verification.EmpiricalBridgeCert
import IndisputableMonolith.Verification.QuantumGravityCert
import IndisputableMonolith.Verification.AppliedScienceCert
import IndisputableMonolith.Verification.AppliedScienceSummary
import IndisputableMonolith.Verification.CategoryMeaningCert
import IndisputableMonolith.Verification.HighPrecisionCert
import IndisputableMonolith.Verification.TwoOutcomeBornCert
import IndisputableMonolith.Verification.UniqueCalibrationCert
import IndisputableMonolith.Verification.UnitNormalizationZeroCert
import IndisputableMonolith.Verification.UnitsFromAnchorsRescaleCert
import IndisputableMonolith.Verification.UnitsRescaledLawsCert
import IndisputableMonolith.Verification.VariationalFoundationCert
import IndisputableMonolith.Verification.WTokenBasisCert
import IndisputableMonolith.Verification.WTokenClassificationCert
import IndisputableMonolith.Verification.WTokenSemanticsCert
import IndisputableMonolith.Verification.WTokenZeroDCCert
import IndisputableMonolith.Verification.WaterHardwareCert

namespace IndisputableMonolith.Verification.NonCircularity

open IndisputableMonolith.RecogSpec

structure NonCircularityCert where
  deriving Repr

@[simp] def NonCircularityCert.verified (_c : NonCircularityCert) : Prop :=
  (∀ φ : ℝ,
      RecogSpec.alphaDefault φ = (1 - 1 / φ) / 2
      ∧ RecogSpec.massRatiosDefault φ = [φ, 1 / (φ ^ (2 : Nat))]
      ∧ RecogSpec.mixingAnglesDefault φ = [1 / φ]
      ∧ RecogSpec.g2Default φ = 1 / (φ ^ (5 : Nat)))
  ∧ (∀ φ : ℝ, URCGenerators.VerifiedGenerators φ)
  ∧ (∀ U : IndisputableMonolith.Constants.RSUnits,
      U.tau0 ≠ 0 →
      U.ell0 ≠ 0 →
        (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K
        ∧ (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K)
  ∧ RecogSpec.bornHolds
  ∧ AdvancedParticlePhysics.AdvancedParticlePhysicsCert.verified {}
  ∧ AlphaDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.Tier2.Tier2Cert.verified {}
  ∧ IndisputableMonolith.Verification.Tier3Cert.verified {}
  ∧ IndisputableMonolith.Verification.Tier6Astrophysics.Tier6Cert.verified {}
  ∧ IndisputableMonolith.Verification.SimplicialFoundation.SimplicialFoundationCert.verified {}
  ∧ IndisputableMonolith.Verification.EmpiricalBridge.EmpiricalBridgeCert.verified {}
  ∧ IndisputableMonolith.Verification.QuantumGravity.QuantumGravityCert.verified {}
  ∧ IndisputableMonolith.Verification.AppliedScience.AppliedScienceCert.verified {}
  ∧ IndisputableMonolith.Verification.CategoryMeaning.CategoryMeaningCert.verified {}
  ∧ IndisputableMonolith.Verification.HighPrecision.HighPrecisionCert.verified {}
  ∧ IndisputableMonolith.Verification.EmpiricalBridgeSummary.empirical_bridge_status = EmpiricalBridgeSummary.empirical_bridge_status
  ∧ IndisputableMonolith.Verification.AppliedScienceSummary.applied_science_status = AppliedScienceSummary.applied_science_status
  ∧ IndisputableMonolith.Verification.VariationalFoundation.VariationalFoundationCert.verified {}
  ∧ IndisputableMonolith.Verification.AnchorsRescaleEqv.AnchorsRescaleEqvCert.verified {}
  ∧ IndisputableMonolith.Verification.AxiomaticOps.AxiomaticOpsCert.verified {}
  ∧ IndisputableMonolith.Verification.BandsInvariant.BandsInvariantCert.verified {}
  ∧ IndisputableMonolith.Verification.BornRuleDerivation.BornRuleDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.CPMConstants.CPMConstantsCert.verified {}
  ∧ IndisputableMonolith.Verification.Calibration.CalibrationCert.verified {}
  ∧ IndisputableMonolith.Verification.CminDerivation.CminDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.ConjTransposeShiftMul.ConjTransposeShiftMulCert.verified {}
  ∧ IndisputableMonolith.Verification.Convexity.ConvexityCert.verified {}
  ∧ IndisputableMonolith.Verification.CoshProperties.CoshPropertiesCert.verified {}
  ∧ IndisputableMonolith.Verification.CoshStrictConvex.CoshStrictConvexCert.verified {}
  ∧ IndisputableMonolith.Verification.CostUniqueness.CostUniquenessCert.verified {}
  ∧ IndisputableMonolith.Verification.CprojDerivation.CprojDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.CubeGeometry.CubeGeometryCert.verified {}
  ∧ IndisputableMonolith.Verification.CurvatureSpace.CurvatureSpaceCert.verified {}
  ∧ IndisputableMonolith.Verification.DAlembertSymmetry.DAlembertSymmetryCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8ColumnOrthonormal.DFT8ColumnOrthonormalCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8DiagonalizesShift.DFT8DiagonalizesShiftCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8EntrySym.DFT8EntrySymCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8ModeNeutral.DFT8ModeNeutralCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8ModeZeroConstant.DFT8ModeZeroConstantCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8RowOrthonormal.DFT8RowOrthonormalCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8ShiftDiagonalization.DFT8ShiftDiagonalizationCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8ShiftEigenvector.DFT8ShiftEigenvectorCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8Symmetry.DFT8SymmetryCert.verified {}
  ∧ IndisputableMonolith.Verification.DFT8Unitary.DFT8UnitaryCert.verified {}
  ∧ IndisputableMonolith.Verification.EightTickFundamental.EightTickFundamentalCert.verified {}
  ∧ IndisputableMonolith.Verification.EightTickLowerBound.EightTickLowerBoundCert.verified {}
  ∧ IndisputableMonolith.Verification.EmpiricalHypotheses.EmpiricalHypothesesCert.verified {}
  ∧ IndisputableMonolith.Verification.EulerLagrange.EulerLagrangeCert.verified {}
  ∧ IndisputableMonolith.Verification.FibSubstCert.FibSubstCert.verified {}
  ∧ IndisputableMonolith.Verification.Gap45Dimension.Gap45DimensionCert.verified {}
  ∧ IndisputableMonolith.Verification.GapWeightDerivation.GapWeightDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.GaugeInvariance.GaugeInvarianceCert.verified {}
  ∧ IndisputableMonolith.Verification.GenerationTorsion.GenerationTorsionCert.verified {}
  ∧ IndisputableMonolith.Verification.HonestClosure.HonestClosureCert.verified {}
  ∧ IndisputableMonolith.Verification.ILGCoercivity.ILGCoercivityCert.verified {}
  ∧ IndisputableMonolith.Verification.JCostAtPhi.JCostAtPhiCert.verified {}
  ∧ IndisputableMonolith.Verification.JCostLightLanguage.JCostLightLanguageCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostAxioms.JcostAxiomsCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostConvexity.JcostConvexityCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostCoshForm.JcostCoshFormCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostCoshIdentity.JcostCoshIdentityCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostMinimum.JcostMinimumCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostMono.JcostMonoCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostNonneg.JcostNonnegCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostNormalization.JcostNormalizationCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostSatisfiesJensen.JcostSatisfiesJensenCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostStrict.JcostStrictCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostStrictConvex.JcostStrictConvexCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostStrictPos.JcostStrictPosCert.verified {}
  ∧ IndisputableMonolith.Verification.JcostSymmetry.JcostSymmetryCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogAMGM.JlogAMGMCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogCosh.JlogCoshCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogDeriv.JlogDerivCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogNonneg.JlogNonnegCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogStrictConvex.JlogStrictConvexCert.verified {}
  ∧ IndisputableMonolith.Verification.JlogZero.JlogZeroCert.verified {}
  ∧ IndisputableMonolith.Verification.KDisplayDimless.KDisplayDimlessCert.verified {}
  ∧ IndisputableMonolith.Verification.KernelMatch.KernelMatchCert.verified {}
  ∧ IndisputableMonolith.Verification.KnetDerivation.KnetDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.LNALCostAdditive.LNALCostAdditiveCert.verified {}
  ∧ IndisputableMonolith.Verification.LambdaRec.LambdaRecDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.LedgerUniqueness.LedgerUniquenessCert.verified {}
  ∧ IndisputableMonolith.Verification.LightLanguageBridge.LightLanguageBridgeCert.verified {}
  ∧ IndisputableMonolith.Verification.MassLaw.MassLawCert.verified {}
  ∧ IndisputableMonolith.Verification.MatchesEval.MatchesEvalCert.verified {}
  ∧ IndisputableMonolith.Verification.MeasurementBridge.MeasurementBridgeCert.verified {}
  ∧ IndisputableMonolith.Verification.MetricCurvature.MetricCurvatureCert.verified {}
  ∧ IndisputableMonolith.Verification.MetricFromUnits.MetricFromUnitsCert.verified {}
  ∧ IndisputableMonolith.Verification.Mod8MulEq.Mod8MulEqCert.verified {}
  ∧ IndisputableMonolith.Verification.NeutralityProjection.NeutralityProjectionCert.verified {}
  ∧ IndisputableMonolith.Verification.NyquistObstruction.NyquistObstructionCert.verified {}
  ∧ IndisputableMonolith.Verification.ODECoshUnique.ODECoshUniqueCert.verified {}
  ∧ IndisputableMonolith.Verification.ODEFoundation.ODEFoundationCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Abs.Omega8AbsCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Conjugate.Omega8ConjugateCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8InvEqPow7.Omega8InvEqPow7Cert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8MulInv.Omega8MulInvCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Pow4.Omega8Pow4Cert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Pow8.Omega8Pow8Cert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8PowerProduct.Omega8PowerProductCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Primitive.Omega8PrimitiveCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Primitivity.Omega8PrimitivityCert.verified {}
  ∧ IndisputableMonolith.Verification.Omega8Properties.Omega8PropertiesCert.verified {}
  ∧ IndisputableMonolith.Verification.OneLtPhi.OneLtPhiCert.verified {}
  ∧ IndisputableMonolith.Verification.PerfectGeneticCode.PerfectGeneticCodeCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiAlgebra.PhiAlgebraCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiAlternativesFail.PhiAlternativesFailCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiBounds.PhiBoundsCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiClosedDefaults.PhiClosedDefaultsCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiDecimalBounds.PhiDecimalBoundsCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiFixedPoint.PhiFixedPointCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiIrrationality.PhiIrrationalityCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiNeZero.PhiNeZeroCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiNecessityCert.PhiNecessityCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiNonDegenerate.PhiNonDegenerateCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiPositivity.PhiPositivityCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiPowerBounds.PhiPowerBoundsCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiSelfSimilarity.PhiSelfSimilarityCert.verified {}
  ∧ IndisputableMonolith.Verification.PhiSquared.PhiSquaredCert.verified {}
  ∧ IndisputableMonolith.Verification.ProbabilityNormalization.ProbabilityNormalizationCert.verified {}
  ∧ IndisputableMonolith.Verification.RSPhysicalModel.RSPhysicalModelCert.verified {}
  ∧ IndisputableMonolith.Verification.RSStructuralDerivation.RSStructuralDerivationCert.verified {}
  ∧ IndisputableMonolith.Verification.ReciprocalSymmetryEven.ReciprocalSymmetryEvenCert.verified {}
  ∧ IndisputableMonolith.Verification.RecognitionComplexity.RecognitionComplexityCert.verified {}
  ∧ IndisputableMonolith.Verification.RootsOfUnitySum.RootsOfUnitySumCert.verified {}
  ∧ IndisputableMonolith.Verification.RootsOfUnitySumZero.RootsOfUnitySumZeroCert.verified {}
  ∧ IndisputableMonolith.Verification.ShiftMulDFT8Entry.ShiftMulDFT8EntryCert.verified {}
  ∧ IndisputableMonolith.Verification.StandardDFT8Basis.StandardDFT8BasisCert.verified {}
  ∧ IndisputableMonolith.Verification.StarDFT8EntryMul.StarDFT8EntryMulCert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8.StarOmega8Cert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8MulSelf.StarOmega8MulSelfCert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8Pow.StarOmega8PowCert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8PowMulPow.StarOmega8PowMulPowCert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8PowMulSame.StarOmega8PowMulSameCert.verified {}
  ∧ IndisputableMonolith.Verification.StarOmega8PowMulSelf.StarOmega8PowMulSelfCert.verified {}
  ∧ IndisputableMonolith.Verification.StructuralDerivationGap.StructuralDerivationGapCert.verified {}
    ∧ IndisputableMonolith.Verification.StructuralPartition.StructuralPartitionCert.verified {}
  ∧ IndisputableMonolith.Verification.SumStarOmega8Prod.SumStarOmega8ProdCert.verified {}
  ∧ IndisputableMonolith.Verification.T5Unique.T5UniqueCert.verified {}
  ∧ IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified {}
  ∧ IndisputableMonolith.Verification.UniqueCalibration.UniqueCalibrationCert.verified {}
  ∧ IndisputableMonolith.Verification.UnitNormalizationZero.UnitNormalizationZeroCert.verified {}
  ∧ IndisputableMonolith.Verification.UnitsFromAnchorsRescale.UnitsFromAnchorsRescaleCert.verified {}
  ∧ IndisputableMonolith.Verification.UnitsRescaledLaws.UnitsRescaledLawsCert.verified {}
  ∧ IndisputableMonolith.Verification.WTokenBasis.WTokenBasisCert.verified {}
  ∧ IndisputableMonolith.Verification.WTokenClassification.WTokenClassificationCert.verified {}
  ∧ IndisputableMonolith.Verification.WTokenSemantics.WTokenSemanticsCert.verified {}
  ∧ IndisputableMonolith.Verification.WTokenZeroDC.WTokenZeroDCCert.verified {}
  ∧ IndisputableMonolith.Verification.WaterHardware.WaterHardwareCert.verified {}
  ∧ IndisputableMonolith.URCGenerators.CPMMethodCert.verified {}

@[simp] theorem NonCircularityCert.verified_any (c : NonCircularityCert) :
    NonCircularityCert.verified c := by
  repeat constructor
  · /--- **CERT(definitional)**: Defaults match their definitions. -/
    intro φ; refine ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩
  · intro φ; exact URCGenerators.demo_generators φ
  · intro U h1 h2; constructor
    · exact (IndisputableMonolith.Constants.RSUnits.K_gate_eqK U h1 h2).1
    · exact (IndisputableMonolith.Constants.RSUnits.K_gate_eqK U h1 h2).2
  · exact RecogSpec.born_from_TruthCore
  · exact AdvancedParticlePhysics.AdvancedParticlePhysicsCert.particle_physics_verified
  · exact AlphaDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.Tier2.Tier2Cert.verified_any {}
  · exact IndisputableMonolith.Verification.Tier3Cert.verified_any {}
  · exact IndisputableMonolith.Verification.Tier6Astrophysics.Tier6Cert.verified_any
  · exact IndisputableMonolith.Verification.SimplicialFoundation.SimplicialFoundationCert.verified_any
  · exact IndisputableMonolith.Verification.EmpiricalBridge.EmpiricalBridgeCert.verified_any
  · exact IndisputableMonolith.Verification.QuantumGravity.QuantumGravityCert.verified_any
  · exact IndisputableMonolith.Verification.AppliedScience.AppliedScienceCert.verified_any
  · exact IndisputableMonolith.Verification.CategoryMeaning.CategoryMeaningCert.verified_any
  · exact IndisputableMonolith.Verification.HighPrecision.HighPrecisionCert.verified_any
  · rfl -- empirical_bridge_status match
  · rfl -- applied_science_status match
  · exact IndisputableMonolith.Verification.VariationalFoundation.VariationalFoundationCert.variational_foundation_verified
  · exact IndisputableMonolith.Verification.AnchorsRescaleEqv.AnchorsRescaleEqvCert.verified_any {}
  · exact IndisputableMonolith.Verification.AxiomaticOps.AxiomaticOpsCert.verified_any {}
  · exact IndisputableMonolith.Verification.BandsInvariant.BandsInvariantCert.verified_any {}
  · exact IndisputableMonolith.Verification.BornRuleDerivation.BornRuleDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.CPMConstants.CPMConstantsCert.verified_any {}
  · exact IndisputableMonolith.Verification.Calibration.CalibrationCert.verified_any {}
  · exact IndisputableMonolith.Verification.CminDerivation.CminDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.ConjTransposeShiftMul.ConjTransposeShiftMulCert.verified_any {}
  · exact IndisputableMonolith.Verification.Convexity.ConvexityCert.verified_any {}
  · exact IndisputableMonolith.Verification.CoshProperties.CoshPropertiesCert.verified_any {}
  · exact IndisputableMonolith.Verification.CoshStrictConvex.CoshStrictConvexCert.verified_any {}
  · exact IndisputableMonolith.Verification.CostUniqueness.CostUniquenessCert.verified_any {}
  · exact IndisputableMonolith.Verification.CprojDerivation.CprojDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.CubeGeometry.CubeGeometryCert.verified_any {}
  · exact IndisputableMonolith.Verification.CurvatureSpace.CurvatureSpaceCert.verified_any {}
  · exact IndisputableMonolith.Verification.DAlembertSymmetry.DAlembertSymmetryCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8ColumnOrthonormal.DFT8ColumnOrthonormalCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8DiagonalizesShift.DFT8DiagonalizesShiftCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8EntrySym.DFT8EntrySymCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8ModeNeutral.DFT8ModeNeutralCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8ModeZeroConstant.DFT8ModeZeroConstantCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8RowOrthonormal.DFT8RowOrthonormalCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8ShiftDiagonalization.DFT8ShiftDiagonalizationCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8ShiftEigenvector.DFT8ShiftEigenvectorCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8Symmetry.DFT8SymmetryCert.verified_any {}
  · exact IndisputableMonolith.Verification.DFT8Unitary.DFT8UnitaryCert.verified_any {}
  · exact IndisputableMonolith.Verification.EightTickFundamental.EightTickFundamentalCert.verified_any {}
  · exact IndisputableMonolith.Verification.EightTickLowerBound.EightTickLowerBoundCert.verified_any {}
  · exact IndisputableMonolith.Verification.EmpiricalHypotheses.EmpiricalHypothesesCert.verified_any
  · exact IndisputableMonolith.Verification.EulerLagrange.EulerLagrangeCert.verified_any {}
  · exact IndisputableMonolith.Verification.FibSubstCert.FibSubstCert.verified_any {}
  · exact IndisputableMonolith.Verification.Gap45Dimension.Gap45DimensionCert.verified_any {}
  · exact IndisputableMonolith.Verification.GapWeightDerivation.GapWeightDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.GaugeInvariance.GaugeInvarianceCert.verified_any {}
  · exact IndisputableMonolith.Verification.GenerationTorsion.GenerationTorsionCert.verified_any {}
  · exact IndisputableMonolith.Verification.HonestClosure.HonestClosureCert.verified_any {}
  · exact IndisputableMonolith.Verification.ILGCoercivity.ILGCoercivityCert.verified_any {}
  · exact IndisputableMonolith.Verification.JCostAtPhi.JCostAtPhiCert.verified_any {}
  · exact IndisputableMonolith.Verification.JCostLightLanguage.JCostLightLanguageCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostAxioms.JcostAxiomsCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostConvexity.JcostConvexityCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostCoshForm.JcostCoshFormCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostCoshIdentity.JcostCoshIdentityCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostMinimum.JcostMinimumCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostMono.JcostMonoCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostNonneg.JcostNonnegCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostNormalization.JcostNormalizationCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostSatisfiesJensen.JcostSatisfiesJensenCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostStrict.JcostStrictCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostStrictConvex.JcostStrictConvexCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostStrictPos.JcostStrictPosCert.verified_any {}
  · exact IndisputableMonolith.Verification.JcostSymmetry.JcostSymmetryCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogAMGM.JlogAMGMCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogCosh.JlogCoshCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogDeriv.JlogDerivCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogNonneg.JlogNonnegCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogStrictConvex.JlogStrictConvexCert.verified_any {}
  · exact IndisputableMonolith.Verification.JlogZero.JlogZeroCert.verified_any {}
  · exact IndisputableMonolith.Verification.KDisplayDimless.KDisplayDimlessCert.verified_any {}
  · exact IndisputableMonolith.Verification.KernelMatch.KernelMatchCert.verified_any {}
  · exact IndisputableMonolith.Verification.KnetDerivation.KnetDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.LNALCostAdditive.LNALCostAdditiveCert.verified_any {}
  · exact IndisputableMonolith.Verification.LambdaRec.LambdaRecDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.LedgerUniqueness.LedgerUniquenessCert.verified_any {}
  · exact IndisputableMonolith.Verification.LightLanguageBridge.LightLanguageBridgeCert.verified_any {}
  · exact IndisputableMonolith.Verification.MassLaw.MassLawCert.verified_any {}
  · exact IndisputableMonolith.Verification.MatchesEval.MatchesEvalCert.verified_any {}
  · exact IndisputableMonolith.Verification.MeasurementBridge.MeasurementBridgeCert.verified_any {}
  · exact IndisputableMonolith.Verification.MetricCurvature.MetricCurvatureCert.verified_any {}
  · exact IndisputableMonolith.Verification.MetricFromUnits.MetricFromUnitsCert.verified_any {}
  · exact IndisputableMonolith.Verification.Mod8MulEq.Mod8MulEqCert.verified_any {}
  · exact IndisputableMonolith.Verification.NeutralityProjection.NeutralityProjectionCert.verified_any {}
  · exact IndisputableMonolith.Verification.NyquistObstruction.NyquistObstructionCert.verified_any {}
  · exact IndisputableMonolith.Verification.ODECoshUnique.ODECoshUniqueCert.verified_any {}
  · exact IndisputableMonolith.Verification.ODEFoundation.ODEFoundationCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Abs.Omega8AbsCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Conjugate.Omega8ConjugateCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8InvEqPow7.Omega8InvEqPow7Cert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8MulInv.Omega8MulInvCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Pow4.Omega8Pow4Cert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Pow8.Omega8Pow8Cert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8PowerProduct.Omega8PowerProductCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Primitive.Omega8PrimitiveCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Primitivity.Omega8PrimitivityCert.verified_any {}
  · exact IndisputableMonolith.Verification.Omega8Properties.Omega8PropertiesCert.verified_any {}
  · exact IndisputableMonolith.Verification.OneLtPhi.OneLtPhiCert.verified_any {}
  · exact IndisputableMonolith.Verification.PerfectGeneticCode.PerfectGeneticCodeCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiAlgebra.PhiAlgebraCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiAlternativesFail.PhiAlternativesFailCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiBounds.PhiBoundsCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiClosedDefaults.PhiClosedDefaultsCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiDecimalBounds.PhiDecimalBoundsCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiFixedPoint.PhiFixedPointCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiIrrationality.PhiIrrationalityCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiNeZero.PhiNeZeroCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiNecessityCert.PhiNecessityCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiNonDegenerate.PhiNonDegenerateCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiPositivity.PhiPositivityCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiPowerBounds.PhiPowerBoundsCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiSelfSimilarity.PhiSelfSimilarityCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiSquared.PhiSquaredCert.verified_any {}
  · exact IndisputableMonolith.Verification.ProbabilityNormalization.ProbabilityNormalizationCert.verified_any {}
  · exact IndisputableMonolith.Verification.RSPhysicalModel.RSPhysicalModelCert.verified_any {}
  · exact IndisputableMonolith.Verification.RSStructuralDerivation.RSStructuralDerivationCert.verified_any {}
  · exact IndisputableMonolith.Verification.ReciprocalSymmetryEven.ReciprocalSymmetryEvenCert.verified_any {}
  · exact IndisputableMonolith.Verification.RecognitionComplexity.RecognitionComplexityCert.verified_any {}
  · exact IndisputableMonolith.Verification.RootsOfUnitySum.RootsOfUnitySumCert.verified_any {}
  · exact IndisputableMonolith.Verification.RootsOfUnitySumZero.RootsOfUnitySumZeroCert.verified_any {}
  · exact IndisputableMonolith.Verification.ShiftMulDFT8Entry.ShiftMulDFT8EntryCert.verified_any {}
  · exact IndisputableMonolith.Verification.StandardDFT8Basis.StandardDFT8BasisCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarDFT8EntryMul.StarDFT8EntryMulCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8.StarOmega8Cert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8MulSelf.StarOmega8MulSelfCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8Pow.StarOmega8PowCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8PowMulPow.StarOmega8PowMulPowCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8PowMulSame.StarOmega8PowMulSameCert.verified_any {}
  · exact IndisputableMonolith.Verification.StarOmega8PowMulSelf.StarOmega8PowMulSelfCert.verified_any {}
  · exact IndisputableMonolith.Verification.StructuralDerivationGap.StructuralDerivationGapCert.verified_any {}
  · exact IndisputableMonolith.Verification.StructuralPartition.StructuralPartitionCert.verified_any {}
  · exact IndisputableMonolith.Verification.SumStarOmega8Prod.SumStarOmega8ProdCert.verified_any {}
  · exact IndisputableMonolith.Verification.T5Unique.T5UniqueCert.verified_any {}
  · exact IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified_any {}
  · exact IndisputableMonolith.Verification.UniqueCalibration.UniqueCalibrationCert.verified_any {}
  · exact IndisputableMonolith.Verification.UnitNormalizationZero.UnitNormalizationZeroCert.verified_any {}
  · exact IndisputableMonolith.Verification.UnitsFromAnchorsRescale.UnitsFromAnchorsRescaleCert.verified_any {}
  · exact IndisputableMonolith.Verification.UnitsRescaledLaws.UnitsRescaledLawsCert.verified_any {}
  · exact IndisputableMonolith.Verification.WTokenBasis.WTokenBasisCert.verified_any {}
  · exact IndisputableMonolith.Verification.WTokenClassification.WTokenClassificationCert.verified_any {}
  · exact IndisputableMonolith.Verification.WTokenSemantics.WTokenSemanticsCert.verified_any {}
  · exact IndisputableMonolith.Verification.WTokenZeroDC.WTokenZeroDCCert.verified_any {}
  · exact IndisputableMonolith.Verification.WaterHardware.WaterHardwareCert.verified_any {}
  · exact IndisputableMonolith.URCGenerators.CPMMethodCert.verified_any {}

end NonCircularity
end Verification
end IndisputableMonolith
