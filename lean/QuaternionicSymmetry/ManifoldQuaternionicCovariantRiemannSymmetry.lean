import QuaternionicSymmetry.ManifoldQuaternionicCovariantMetricSkew
import QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannAlgebra
import QuaternionicSymmetry.AlgebraicRiemannPairSymmetry

/-! Full pair symmetries of the covariant derivative of the actual tangent
Riemann tensor. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicCovariantMetricSkew
open ManifoldQuaternionicCovariantRiemannAlgebra
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- Five-slot covariant derivative of the genuine Riemann tensor, in the
chart basis and evaluated against the genuine chart metric. -/
def covariantRiemann (p : M) (y a u v w z : E) : ℝ :=
  coordinateMetricField Q p y
    (covariantRiemannDerivative (coordinateConnection Q D p) y a u v w) z

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem covariantRiemann_skew_first (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w z : E) :
    covariantRiemann Q D p y a u v w z =
      -covariantRiemann Q D p y a v u w z := by
  rw [covariantRiemann, covariantRiemann,
    ManifoldQuaternionicCovariantRiemannAlgebra.covariantRiemann_skew_first Q D p y hy]
  simp

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem covariantRiemann_skew_last (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w z : E) :
    covariantRiemann Q D p y a u v w z =
      -covariantRiemann Q D p y a u v z w := by
  have h₁ := coordinate_covariantCurvature_metric_skew Q D p y hy a u v w z
  have h₂ := coordinate_curvature_metric_skew Q D p y hy
    (coordinateConnection Q D p y a u) v w z
  have h₃ := coordinate_curvature_metric_skew Q D p y hy
    u (coordinateConnection Q D p y a v) w z
  have hsym (b c : E) : coordinateMetricField Q p y b c =
      coordinateMetricField Q p y c b := by
    rw [coordinateMetricField_apply Q p y hy,
      coordinateMetricField_apply Q p y hy]
    exact real_inner_comm _ _
  unfold covariantRiemann
  rw [hsym (covariantRiemannDerivative (coordinateConnection Q D p) y a u v z) w]
  unfold covariantRiemannDerivative
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  linear_combination h₁ - h₂ - h₃

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem covariantRiemann_first_bianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w z : E) :
    covariantRiemann Q D p y a u v w z +
      covariantRiemann Q D p y a v w u z +
        covariantRiemann Q D p y a w u v z = 0 := by
  have h := congrArg (fun t : E => coordinateMetricField Q p y t z)
    (ManifoldQuaternionicCovariantRiemannAlgebra.covariantRiemann_first_bianchi
      Q D p y hy a u v w)
  simpa only [covariantRiemann, map_add, map_zero] using h

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pair interchange for the covariant derivative of the actual Riemann
tensor. This is the symmetry used by the finite Schur contraction. -/
theorem covariantRiemann_pair_symmetry (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w z : E) :
    covariantRiemann Q D p y a u v w z =
      covariantRiemann Q D p y a w z u v :=
  AlgebraicRiemannPairSymmetry.pair_symmetry
    (covariantRiemann Q D p y a)
    (covariantRiemann_skew_first Q D p y hy a)
    (covariantRiemann_skew_last Q D p y hy a)
    (covariantRiemann_first_bianchi Q D p y hy a) u v w z

end
end QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannSymmetry
