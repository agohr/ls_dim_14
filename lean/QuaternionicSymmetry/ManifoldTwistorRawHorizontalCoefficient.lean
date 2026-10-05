import QuaternionicSymmetry.ManifoldTwistorContactSplitting
import QuaternionicSymmetry.ManifoldTwistorPreferredRawCoordinates

/-! A raw-coordinate formula for the connection-horizontal kernel map,
avoiding dependent comparisons of the two sphere-total-space atlases. -/

namespace QuaternionicSymmetry.ManifoldTwistorRawHorizontalCoefficient
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorHorizontalConnection
open ManifoldTwistorVerticalComplex
open ManifoldTwistorPreferredRawCoordinates
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def rawHorizontalCoefficient (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : geometricSphere) :
    (E × EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ]
      verticalSubmodule (coefficientSphereHomeomorph.symm a) :=
  (LinearMap.snd ℝ E
    (verticalSubmodule (coefficientSphereHomeomorph.symm a))).comp
      ((rawPreferredEquiv (E := E) a).trans
        (connectionSplit Q D p y hy (coefficientSphereHomeomorph.symm a))).toLinearMap

theorem connectionTangentEquiv_second_raw (z : SphereBundleTotal Q)
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    (connectionTangentEquiv Q D z v).2 =
      rawHorizontalCoefficient Q D z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
        ((extChartAt 𝓘(ℝ,E) z.1).map_source
          (mem_extChartAt_source z.1)) z.2 v := by
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorRawHorizontalCoefficient
