import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative
import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

/-! Literal topology and real smooth atlas equality for a constant
homothety of the actual twistor sphere bundle. These are equalities of the
independently constructed bundle structures, not transported definitions. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorAtlasEquality
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private theorem coreTopology_eq
    (Z W : FiberBundleCore (atlas E M) M
      ManifoldTwistorCoefficientSphere.geometricSphere) (h : Z = W) :
    Z.toTopologicalSpace = W.toTopologicalSpace := by
  cases h
  rfl

private theorem coreCharts_transport
    (Z W : FiberBundleCore (atlas E M) M
      ManifoldTwistorCoefficientSphere.geometricSphere) (h : Z = W) :
    h ▸ coreCharts Z = coreCharts W := by
  cases h
  rfl

theorem sphereTopology_rescale (s : ℝ) (hs : s ≠ 0) :
    (inferInstance : TopologicalSpace (SphereBundleTotal (rescaleMetric Q s hs))) =
      (inferInstance : TopologicalSpace (SphereBundleTotal Q)) := by
  exact coreTopology_eq (sphereCore (rescaleMetric Q s hs)) (sphereCore Q)
    (sphereCore_rescale Q s hs)

theorem sphereRealCharts_rescale (s : ℝ) (hs : s ≠ 0) :
    (sphereCore_rescale Q s hs) ▸
      coreCharts (sphereCore (rescaleMetric Q s hs)) =
        coreCharts (sphereCore Q) :=
  coreCharts_transport _ _ (sphereCore_rescale Q s hs)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorAtlasEquality
