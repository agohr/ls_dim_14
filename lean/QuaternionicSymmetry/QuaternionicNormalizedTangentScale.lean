import QuaternionicSymmetry.QuaternionicNormalizedTangentExteriorValue
import QuaternionicSymmetry.QuaternionicScaledBinomialNormalization

namespace QuaternionicSymmetry.QuaternionicNormalizedTangentScale
open QuaternionicNormalizedTangentExteriorValue
  QuaternionicExteriorEvenTrace
  QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicTangentUniversalSpecialization
  HomogeneousMatrixCombinations
  ManifoldEvenClosedEvaluation
  ManifoldClosedTangentGenerators
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem tangentTraceScale_eq_normalization_pow (j : ℕ) :
    ManifoldTangentTraceRootCandidates.tangentTraceScale j =
      QuaternionicQuarterUExteriorValue.normalization ^ j := by
  unfold ManifoldTangentTraceRootCandidates.tangentTraceScale
    QuaternionicQuarterUExteriorValue.normalization
  rw [one_div_pow, pow_mul]

theorem normalizedTangentGrade_scaled (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    gradeValue p y (ContinuousLinearMap.id ℝ E) (k+1)
      (normalizedTangentGrade Q D k) =
    QuaternionicScaledBinomialNormalization.scaledTangentHalfTrace
      (algebraMap ℝ (EvenAlgebra E)
        QuaternionicQuarterUExteriorValue.normalization)
      (spMatrix (chartStructure Q p) (actualEta Q D p y))
      (scalarMatrix (chartStructure Q p) (actualEta Q D p y)) (k+1) := by
  rw [normalizedTangentGrade_value Q D p y hy k]
  rw [tangentTraceScale_eq_normalization_pow]
  unfold QuaternionicScaledBinomialNormalization.scaledTangentHalfTrace
  have hs : QuaternionicQuarterUExteriorValue.normalization ^ (k+1) *
      ((-1 : ℝ) ^ (k+1) / 2) =
      (-QuaternionicQuarterUExteriorValue.normalization) ^ (k+1) * (1/2 : ℝ) := by
    rw [neg_pow]
    ring
  rw [hs]
  let f : ℝ →+* (EvenAlgebra E) := algebraMap ℝ (EvenAlgebra E)
  change f ((-QuaternionicQuarterUExteriorValue.normalization) ^ (k+1) * (1/2 : ℝ)) * _ = _
  rw [f.map_mul, f.map_pow, f.map_neg]
  have hhalf : algebraMap ℝ (EvenAlgebra E) (1/2 : ℝ) =
      algebraMap ℚ (EvenAlgebra E) (1/2 : ℚ) := by
    have hr : (algebraMap ℚ ℝ) (1/2:ℚ) = (1/2:ℝ) := by norm_num
    simpa only [hr] using
      (IsScalarTower.algebraMap_apply ℚ ℝ (EvenAlgebra E) (1/2:ℚ)).symm
  rw [hhalf]

end
end QuaternionicSymmetry.QuaternionicNormalizedTangentScale
