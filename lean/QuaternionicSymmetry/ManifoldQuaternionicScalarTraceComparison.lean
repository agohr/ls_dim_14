import QuaternionicSymmetry.ManifoldQuaternionicTraceSquareSplitting
import QuaternionicSymmetry.ManifoldQuaternionicCurvaturePreservesSpan
import QuaternionicSymmetry.QuaternionicScalarTrace

/-! Exact normalization between the scalar tangent curvature trace and
the trace of the genuine induced rank-three curvature. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicScalarTraceComparison

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  ManifoldQuaternionicCurvatureProjection ManifoldQuaternionicCurvatureSplitting
  ManifoldQuaternionicSymplecticCurvature ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicAdjointCurvature QuaternionicScalarTrace
  LocalEndomorphismTrace LocalChernWeilQuadratic LocalTraceSquareAlgebra
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem inducedCurvature_eq_scalarAdjoint (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inducedCurvature Q D p y u v =
      adjointRepresentation (Q.reduction.Q (achart E p))
        (LocalConnection.curvature (scalarConnection Q D p) y u v) := by
  have hz : adjointRepresentation (Q.reduction.Q (achart E p))
      (LocalConnection.curvature (symplecticConnection Q D p) y u v) = 0 :=
    QuaternionicLieAlgebraProjection.adjointRepresentation_eq_zero_of_commutes _ _
      (symplecticCurvature_commutes Q D p y u v hy)
  rw [inducedCurvature_eq_adjoint Q D p y u v hy, curvature_split Q D p y hy]
  simp only [ContinuousLinearMap.add_apply, map_add, hz, zero_add]

theorem scalar_curvature_product_trace (p : M) (y u v a b : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceCLM (LocalConnection.curvature (scalarConnection Q D p) y u v *
      LocalConnection.curvature (scalarConnection Q D p) y a b) =
      ((Module.finrank ℝ E : ℝ) / 8) *
        traceCLM (inducedCurvature Q D p y u v * inducedCurvature Q D p y a b) := by
  rw [inducedCurvature_eq_scalarAdjoint Q D p y u v hy,
    inducedCurvature_eq_scalarAdjoint Q D p y a b hy,
    scalarCurvature_eq_projection Q D p y u v hy,
    scalarCurvature_eq_projection Q D p y a b hy]
  exact trace_synth_product_eq_adjoint (Q.reduction.Q (achart E p)) _ _

theorem scalar_traceSquareForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceSquareForm traceCLM (scalarConnection Q D p) y =
      ((Module.finrank ℝ E : ℝ) / 8) • traceSquareForm traceCLM (inducedForm Q D p) y := by
  ext w
  have hw : w = ![w 0, w 1, w 2, w 3] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [ContinuousAlternatingMap.smul_apply,
    traceSquareForm_apply traceCLM traceCLM_cyclic, traceSquare4, map_add, map_sub]
  rw [scalar_curvature_product_trace Q D p y _ _ _ _ hy,
    scalar_curvature_product_trace Q D p y _ _ _ _ hy,
    scalar_curvature_product_trace Q D p y _ _ _ _ hy]
  change (2 : ℝ) • (_ * _ - _ * _ + _ * _) = _ • ((2 : ℝ) • (_ - _ + _))
  simp only [smul_eq_mul, inducedCurvature]
  ring

theorem tangent_traceSquareForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceSquareForm traceCLM (D.form p) y =
      traceSquareForm traceCLM (symplecticConnection Q D p) y +
        ((Module.finrank ℝ E : ℝ) / 8) • traceSquareForm traceCLM (inducedForm Q D p) y := by
  rw [ManifoldQuaternionicTraceSquareSplitting.traceSquareForm_split Q D p y hy,
    scalar_traceSquareForm Q D p y hy]

end
end QuaternionicSymmetry.ManifoldQuaternionicScalarTraceComparison
