import QuaternionicSymmetry.ManifoldQuaternionicConnectionSplitting
import QuaternionicSymmetry.LocalConnectionSkewCurvature

/-! Metricity of the actual tangent curvature and of both components of
the quaternionic connection. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentCurvature_skew (p : M) (y u t v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inner ℝ (D.curvature Q p y u t v) w + inner ℝ v (D.curvature Q p y u t w) = 0 := by
  have hd : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  exact LocalConnection.curvature_skew (D.form p) y u t hd (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy] with z hz
    intro t v w
    exact D.metric p z t v w hz) v w

theorem scalarCurvature_skew (p : M) (y u t v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inner ℝ (LocalConnection.curvature (scalarConnection Q D p) y u t v) w +
      inner ℝ v (LocalConnection.curvature (scalarConnection Q D p) y u t w) = 0 := by
  have hd : DifferentiableAt ℝ (scalarConnection Q D p) y :=
    ((scalarConnection_smooth Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  exact LocalConnection.curvature_skew _ y u t hd
    (Filter.Eventually.of_forall fun z t v w => scalarConnection_skew Q D p z t v w) v w

theorem symplecticCurvature_skew (p : M) (y u t v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inner ℝ (LocalConnection.curvature (symplecticConnection Q D p) y u t v) w +
      inner ℝ v (LocalConnection.curvature (symplecticConnection Q D p) y u t w) = 0 := by
  have hd : DifferentiableAt ℝ (symplecticConnection Q D p) y :=
    ((symplecticConnection_smooth Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  exact LocalConnection.curvature_skew _ y u t hd (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy] with z hz
    intro t v w
    exact symplecticConnection_skew Q D p z t v w hz) v w

end
end QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature
