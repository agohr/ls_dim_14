import QuaternionicSymmetry.QuaternionicManifoldModelProjection
import QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

/-! On the actual compatible tangent connection, the adapted-chart
standard Lie form agrees with the fixed-model representation applied after
the constant quaternionic model gauge. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison

open QuaternionicManifoldModelProjection
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicProjectiveStandardLie
  ManifoldQuaternionicConnectionSplitting
  QuaternionicLieAlgebraProjection
  QuaternionicIsometryNormalizer
  ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem standardConnection_eq_standardLie (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    standardConnection S Q D p y u =
      standardLie S (fixedTangentConjugation S Q p (D.form p y u)) := by
  let T := Q.reduction.Q (achart E p)
  let A := D.form p y u
  have hcomm (a : Fin 3 → ℝ) :
      symplecticProjection T A * synth T a =
        synth T a * symplecticProjection T A := by
    exact symplecticConnection_commutes Q D p y u hy a
  have hproj := symplecticProjection_modelGauge S T A hcomm
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change conjugation (QuaternionicManifoldFixedNormalizer.modelGauge S T).symm
        (symplecticProjection T A) z.fst =
      symplecticProjection S (fixedTangentConjugation S Q p A) z.fst
    exact congrArg (fun F : E →L[ℝ] E => F z.fst) hproj.symm
  · rfl

end
end QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison
