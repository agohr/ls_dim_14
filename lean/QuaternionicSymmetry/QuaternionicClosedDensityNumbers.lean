import QuaternionicSymmetry.ManifoldQuaternionicDensityIntegrals
import QuaternionicSymmetry.QuaternionicClosedSourceNumbers

/-! The actual density integrals equal the parameter-independent source polynomial numbers. -/
namespace QuaternionicSymmetry.QuaternionicClosedDensityNumbers
open Module ManifoldQuaternionicDensityIntegrals QuaternionicClosedDensityForms
open QuaternionicClosedSourceNumbers QuaternionicClosedSourceGenerators
open ManifoldRecoveredElevenTwelveWeights ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicIntegralLowerBound
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem density11_sourceNumber_eq_integral
    (hn : S.quaternionicDimension = 11) (t : ℝ) :
    sourcePolynomialNumber S Q D t 10
      (show 4*(10+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) =
      integral Q (density11Top (Q := Q) (D := D) S hn t) := by
  simpa only [density11Top, density11Form] using
    sourcePolynomialNumber_representative S Q D t 10
      (show 4*(10+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11)
      lifted_density11_weighted

theorem density12_sourceNumber_eq_integral
    (hn : S.quaternionicDimension = 12) (t : ℝ) :
    sourcePolynomialNumber S Q D t 11
      (show 4*(11+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) =
      integral Q (density12Top (Q := Q) (D := D) S hn t) := by
  simpa only [density12Top, density12Form] using
    sourcePolynomialNumber_representative S Q D t 11
      (show 4*(11+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12)
      lifted_density12_weighted

end
end QuaternionicSymmetry.QuaternionicClosedDensityNumbers
