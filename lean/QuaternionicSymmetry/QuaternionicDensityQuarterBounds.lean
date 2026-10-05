import QuaternionicSymmetry.QuaternionicClosedDensityNumbers
import QuaternionicSymmetry.ManifoldQuaternionicQuarterVolume

/-! The C12 scalar reserves as canonical inequalities against the actual
top wedge power of the analytic quarter-Pontryagin form. -/
namespace QuaternionicSymmetry.QuaternionicDensityQuarterBounds
open Module ManifoldQuaternionicDensityIntegrals QuaternionicClosedDensityNumbers
open QuaternionicClosedSourceNumbers ManifoldQuaternionicQuarterVolume
open ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem density11_sourceNumber_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t^2) (s : ℝ) :
    288 * integral Q (quarterTop Q D 11 (by have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S Q D s 10 (by have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) := by
  rw [sourcePolynomialNumber_parameter_independent S Q D t s,
    density11_sourceNumber_eq_integral S Q D hn t,
    quarterTop_integral_normalized Q D S hsp t ht, ← mul_assoc]
  exact density11_integral_lower_bound S Q D hsource hsp hdecomp hn
    (Module.finBasis ℝ E) t htpos ht

theorem density12_sourceNumber_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t^2) (s : ℝ) :
    336 * integral Q (quarterTop Q D 12 (by have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S Q D s 11 (by have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) := by
  rw [sourcePolynomialNumber_parameter_independent S Q D t s,
    density12_sourceNumber_eq_integral S Q D hn t,
    quarterTop_integral_normalized Q D S hsp t ht, ← mul_assoc]
  exact density12_integral_lower_bound S Q D hsource hsp hdecomp hn
    (Module.finBasis ℝ E) t htpos ht

end
end QuaternionicSymmetry.QuaternionicDensityQuarterBounds
