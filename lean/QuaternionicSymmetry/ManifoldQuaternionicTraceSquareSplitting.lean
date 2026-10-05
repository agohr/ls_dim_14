import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.QuaternionicTraceOrthogonality
import QuaternionicSymmetry.LocalChernWeilQuadratic

/-! The actual degree-four tangent trace form splits into its symplectic
and scalar parts, with mixed traces proved to vanish. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTraceSquareSplitting

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  ManifoldQuaternionicCurvatureProjection ManifoldQuaternionicCurvatureSplitting
  ManifoldQuaternionicSymplecticCurvature QuaternionicTraceOrthogonality
  LocalEndomorphismTrace LocalChernWeilQuadratic LocalTraceSquareAlgebra
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem mixed_curvature_trace_zero (p : M) (y u v a b : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceCLM (LocalConnection.curvature (symplecticConnection Q D p) y u v *
      LocalConnection.curvature (scalarConnection Q D p) y a b) = 0 := by
  rw [scalarCurvature_eq_projection Q D p y a b hy]
  exact trace_mul_synth (Q.reduction.Q (achart E p)) _
    (symplecticCurvature_commutes Q D p y u v hy) _

theorem curvature_product_trace_split (p : M) (y u v a b : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceCLM (D.curvature Q p y u v * D.curvature Q p y a b) =
      traceCLM (LocalConnection.curvature (symplecticConnection Q D p) y u v *
        LocalConnection.curvature (symplecticConnection Q D p) y a b) +
      traceCLM (LocalConnection.curvature (scalarConnection Q D p) y u v *
        LocalConnection.curvature (scalarConnection Q D p) y a b) := by
  rw [curvature_split Q D p y hy]
  simp only [ContinuousLinearMap.add_apply, add_mul, mul_add, map_add]
  rw [mixed_curvature_trace_zero Q D p y u v a b hy,
    traceCLM_cyclic (LocalConnection.curvature (scalarConnection Q D p) y u v),
    mixed_curvature_trace_zero Q D p y a b u v hy]
  abel

theorem traceSquareForm_split (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    traceSquareForm traceCLM (D.form p) y =
      traceSquareForm traceCLM (symplecticConnection Q D p) y +
        traceSquareForm traceCLM (scalarConnection Q D p) y := by
  ext w
  have hw : w = ![w 0, w 1, w 2, w 3] := by ext i; fin_cases i <;> rfl
  rw [hw]
  simp only [ContinuousAlternatingMap.add_apply,
    traceSquareForm_apply traceCLM traceCLM_cyclic, traceSquare4, map_add, map_sub]
  change (2 : ℝ) • (traceCLM (D.curvature Q p y _ _ * D.curvature Q p y _ _) -
      traceCLM (D.curvature Q p y _ _ * D.curvature Q p y _ _) +
      traceCLM (D.curvature Q p y _ _ * D.curvature Q p y _ _)) = _
  rw [curvature_product_trace_split Q D p y _ _ _ _ hy,
    curvature_product_trace_split Q D p y _ _ _ _ hy,
    curvature_product_trace_split Q D p y _ _ _ _ hy]
  module

end
end QuaternionicSymmetry.ManifoldQuaternionicTraceSquareSplitting
