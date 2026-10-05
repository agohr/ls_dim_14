import QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace
import QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
import QuaternionicSymmetry.ManifoldQuaternionicScalarTraceComparison

/-! The real quadratic trace of actual projective-standard curvature equals
the symplectic tangent trace plus one half of the induced rank-three trace. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardTraceSquare

open QuaternionicFixedModelAdjointTrace
  QuaternionicManifoldStandardCurvatureRepresentation
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicConnection
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicCurvatureProjection
  ManifoldQuaternionicSymplecticCurvature
  ManifoldQuaternionicAdjointCurvature
  ManifoldQuaternionicAdjointConnection
  LocalEndomorphismTrace
  LocalChernWeilQuadratic
  LocalTraceSquareAlgebra
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem standardCurvature_product_trace (p : M) (y u v a b : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceCLM
      (LocalConnection.curvature (standardConnection S Q D p) y u v *
        LocalConnection.curvature (standardConnection S Q D p) y a b) =
      traceCLM
        (LocalConnection.curvature (symplecticConnection Q D p) y u v *
          LocalConnection.curvature (symplecticConnection Q D p) y a b) +
      (1 / 2 : ℝ) *
        traceCLM (inducedCurvature Q D p y u v * inducedCurvature Q D p y a b) := by
  rw [standardCurvature_eq_representation S Q D p y u v hy,
    standardCurvature_eq_representation S Q D p y a b hy]
  let T := Q.reduction.Q (achart E p)
  let A := D.curvature Q p y u v
  let B := D.curvature Q p y a b
  have hA : ∀ c, QuaternionicLieAlgebraProjection.symplecticProjection T A *
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c =
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c *
          QuaternionicLieAlgebraProjection.symplecticProjection T A := by
    intro c
    rw [← symplecticCurvature_eq_projection Q D p y u v hy]
    exact symplecticCurvature_commutes Q D p y u v hy c
  have hB : ∀ c, QuaternionicLieAlgebraProjection.symplecticProjection T B *
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c =
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c *
          QuaternionicLieAlgebraProjection.symplecticProjection T B := by
    intro c
    rw [← symplecticCurvature_eq_projection Q D p y a b hy]
    exact symplecticCurvature_commutes Q D p y a b hy c
  have ht := standardLie_fixed_product_trace S T A B hA hB
  rw [← symplecticCurvature_eq_projection Q D p y u v hy,
    ← symplecticCurvature_eq_projection Q D p y a b hy] at ht
  rw [inducedCurvature_eq_adjoint Q D p y u v hy,
    inducedCurvature_eq_adjoint Q D p y a b hy]
  exact ht

set_option maxHeartbeats 800000 in
theorem standard_traceSquareForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceSquareForm traceCLM (standardConnection S Q D p) y =
      traceSquareForm traceCLM (symplecticConnection Q D p) y +
        (1 / 2 : ℝ) • traceSquareForm traceCLM (inducedForm Q D p) y := by
  ext w
  have hw : w = ![w 0, w 1, w 2, w 3] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply,
    traceSquareForm_apply traceCLM traceCLM_cyclic, traceSquare4,
    map_add, map_sub]
  rw [standardCurvature_product_trace S Q D p y _ _ _ _ hy,
    standardCurvature_product_trace S Q D p y _ _ _ _ hy,
    standardCurvature_product_trace S Q D p y _ _ _ _ hy]
  simp only [smul_eq_mul, inducedCurvature]
  ring

end
end QuaternionicSymmetry.QuaternionicManifoldStandardTraceSquare
