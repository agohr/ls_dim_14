import QuaternionicSymmetry.ManifoldQuaternionicCoordinateSecondBianchi
import QuaternionicSymmetry.LocalConnectionCovariantRiemannAlgebra
import QuaternionicSymmetry.LocalConnectionFirstBianchi

/-! The covariant derivative of the genuine tangent Riemann curvature has
its first algebraic symmetries in the original manifold chart coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannAlgebra
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicCoordinateSecondBianchi
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionFirstBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open QuaternionicSymmetry.LocalConnectionCovariantRiemannAlgebra
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

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem coordinate_symmetry_eventually (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    (fun z => coordinateConnection Q D p z u v) =ᶠ[𝓝 y]
      (fun z => coordinateConnection Q D p z v u) := by
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
    with z hz
  exact coordinateConnection_symmetric Q D p z hz u v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem coordinate_first_bianchi_eventually (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    (fun z => curvature (coordinateConnection Q D p) z u v w +
      curvature (coordinateConnection Q D p) z v w u +
        curvature (coordinateConnection Q D p) z w u v) =ᶠ[𝓝 y]
      fun _ => 0 := by
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
    with z hz
  exact first_bianchi (coordinateConnection Q D p) z
    ((coordinateConnection_contDiffAt Q D p z hz).differentiableAt (by norm_num))
    (coordinate_symmetry_eventually Q D p z hz) u v w

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Algebraic first Bianchi for the actual covariant derivative of the
coordinate Riemann tensor. -/
theorem covariantRiemann_first_bianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w : E) :
    covariantRiemannDerivative (coordinateConnection Q D p) y a u v w +
      covariantRiemannDerivative (coordinateConnection Q D p) y a v w u +
        covariantRiemannDerivative (coordinateConnection Q D p) y a w u v = 0 :=
  covariantRiemannDerivative_first_bianchi (coordinateConnection Q D p) y
    (coordinateConnection_contDiffAt Q D p y hy)
    (coordinate_first_bianchi_eventually Q D p y hy) a u v w

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Skewness in the first curvature pair. -/
theorem covariantRiemann_skew_first (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a u v w : E) :
    covariantRiemannDerivative (coordinateConnection Q D p) y a u v w =
      -covariantRiemannDerivative (coordinateConnection Q D p) y a v u w :=
  covariantRiemannDerivative_antisymm (coordinateConnection Q D p) y
    (coordinateConnection_symmetric Q D p y hy) a u v w

end
end QuaternionicSymmetry.ManifoldQuaternionicCovariantRiemannAlgebra
