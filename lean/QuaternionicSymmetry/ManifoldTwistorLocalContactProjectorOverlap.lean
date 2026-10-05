import QuaternionicSymmetry.ManifoldTwistorLocalContactProjectorSmooth
import QuaternionicSymmetry.ManifoldTwistorRawComplexCovariance

/-! The connection horizontal projection commutes with the actual twistor
raw-chart tangent transition. This is the bundle-gluing identity needed for
the global smooth contact-distribution projector. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

def localHorizontalPlaneProjection (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a : coefficientSphere) :
    (E × verticalSubmodule a) →ₗ[ℝ] (E × verticalSubmodule a) :=
  (horizontalLift Q D p y hy a).comp (LinearMap.fst ℝ E (verticalSubmodule a))

theorem localHorizontalPlaneProjection_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (a : coefficientSphere)
    (uv : E × verticalSubmodule a) :
    localHorizontalPlaneProjection Q D p y hy a uv =
      (uv.1,-connectionVertical Q D p y hy a uv.1) := rfl

theorem localTangentTransition_horizontalLift (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (u : E) :
    localTangentTransition Q D p q y hy a
      (horizontalLift Q D p y hy.1 a u) =
      horizontalLift Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        (rotatedCoefficient Q p q y hy a)
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u) := by
  simp [localTangentTransition, splitTransition,
    horizontalLift, connectionSplit]

theorem localTangentTransition_horizontalProjection (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    localTangentTransition Q D p q y hy a
      (localHorizontalPlaneProjection Q D p y hy.1 a uv) =
      localHorizontalPlaneProjection Q D q
        (chartTransition (I := 𝓘(ℝ,E)) p q y)
        ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        (rotatedCoefficient Q p q y hy a)
        (localTangentTransition Q D p q y hy a uv) := by
  rw [localHorizontalPlaneProjection_apply]
  have h := localTangentTransition_horizontalLift Q D p q y hy a uv.1
  change localTangentTransition Q D p q y hy a
      (horizontalLift Q D p y hy.1 a uv.1) = _ at h ⊢
  rw [h]
  simp [localHorizontalPlaneProjection, localTangentTransition,
    splitTransition, connectionSplit]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
